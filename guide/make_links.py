#!/usr/bin/env python3
"""Write the overlay's annotations from the boxes the guide records, and check line coverage.

`reading-guide.tex` wraps every linked formula, symbol and diagram node in
`\\lk[title]{targets}{content}`. At shipout pdfTeX records, for each one, the
page and the exact box it occupies (`reading-guide.lk`, one line per box:
number|page|x sp|y sp|width|height|depth|section|title|targets). This script

1. resolves every target to lines of the Lean library:
   - `Name` (under the namespace `VoltageToBit`): a declaration, from its doc
     comment to its last line; for a structure, its doc comment and header only;
   - `Struct.field`: one field of a structure, with its doc comment;
   - `Name@field`: the line `field := ...` of a definition written with `where`;
   - `mod:Path` (`mod:Model/Inverter`, or `mod:VoltageToBit` for the root
     file): the module's structural lines, that is every run of lines outside
     its declarations (imports, header comment, namespaces, section comments);
2. checks that no two boxes on a page overlap, and that the links together
   cover every non-blank line of every Lean file of the library (it exits 1
   and lists the lines if not);
3. writes Literature Links 1.0.1 records into `annotations/`, one per
   (box, linked range), with the box as the PDF end and the lines as the Lean end.

    python3 guide/make_links.py --check            # resolve, overlap and coverage only
    python3 guide/make_links.py --commit <sha>     # also write annotations/

The commit must hold the PDF this script reads (its sha256 is compared with
the committed file) and is the version the Lean links point into.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
LIB = "VoltageToBit"
REPO = "https://github.com/Deicyde/voltage-to-bit"
RAW = "https://raw.githubusercontent.com/Deicyde/voltage-to-bit"
PDF = HERE / "reading-guide.pdf"
LK = HERE / "reading-guide.lk"
OUT = ROOT / "annotations"
NS = "org.mathlib-initiative.formal-companion.overlay"
SOURCE_ID = "voltage-to-bit-reading-guide"
SOURCE_TITLE = "voltage-to-bit: the specification and its proof"
PAD = 0.75  # pt added on each side of a recorded box
SP_PER_PT = 65536

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|nonrec)\s+)*)"
                  r"(?P<kw>theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+(?P<name>[^\s(:{\[]+)")
NAMESPACE = re.compile(r"^namespace\s+(\S+)")
END = re.compile(r"^end(?:\s+(\S+))?\s*$")
SECTION = re.compile(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
FIELD = re.compile(r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*:(?!=)")
WHERE_FIELD = re.compile(r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*:=")


@dataclass
class Span:
    path: str            # repository-relative path of the Lean file
    module: str          # dotted module name
    first: int           # 1-based, inclusive
    last: int
    name: str | None     # declaration (or field) name; None for structural lines
    kind: str
    snippet: str
    title: str = ""
    private: bool = False
    part: str = ""       # "", "header" (of a structure), "field", or "line" (of a definition)


@dataclass
class LeanFile:
    path: str
    module: str
    lines: list[str]
    decls: dict[str, Span] = field(default_factory=dict)       # whole declarations
    targets: dict[str, Span] = field(default_factory=dict)     # names a link may give
    frames: list[Span] = field(default_factory=list)


def blank(line: str) -> bool:
    return not line.strip()


def trim(lines: list[str], first: int, last: int) -> tuple[int, int]:
    while last > first and blank(lines[last - 1]):
        last -= 1
    while first < last and blank(lines[first - 1]):
        first += 1
    return first, last


def statement(lines: list[str], first: int, last: int, kind: str) -> str:
    block = lines[first - 1:last]
    if kind in ("def", "abbrev", "structure", "instance", "class", "inductive"):
        cap = 60
    else:
        cap = 14
        for i, line in enumerate(block):
            if ":=" in line:
                block = block[:i] + [line[:line.index(":=") + 2] + (" by" if line.rstrip().endswith("by") else "")]
                break
            if line.rstrip().endswith(" where"):
                block = block[:i + 1]
                break
    if len(block) > cap:
        block = block[:cap] + ["  …"]
    return "\n".join(block).rstrip()


def doc_start(lines: list[str], kw: int) -> int:
    """The first line of the attributes and doc comment right above the keyword line kw (1-based)."""
    j = kw - 1
    while j >= 1 and lines[j - 1].lstrip().startswith("@["):
        j -= 1
    if j >= 1 and lines[j - 1].rstrip().endswith("-/"):
        k = j
        while k >= 1:
            text = lines[k - 1].lstrip()
            if text.startswith("/--"):
                return k
            if text.startswith("/-") or (k < j and lines[k - 1].rstrip().endswith("-/")):
                break
            k -= 1
    return j + 1


def parse(path: Path) -> LeanFile:
    rel = path.relative_to(ROOT).as_posix()
    module = rel[:-len(".lean")].replace("/", ".")
    lines = path.read_text(encoding="utf-8").split("\n")
    if lines and lines[-1] == "":
        lines = lines[:-1]
    lf = LeanFile(rel, module, lines)
    stack: list[list[str]] = []
    starts: list[tuple[int, re.Match[str], str]] = []
    depth = 0
    for n, line in enumerate(lines, start=1):
        opened, closed = line.count("/-"), line.count("-/")
        in_comment = depth > 0
        depth = max(0, depth + opened - closed)
        if in_comment or line[:1] in (" ", "\t", ""):
            continue
        if m := NAMESPACE.match(line):
            stack.append(m.group(1).split("."))
        elif SECTION.match(line):
            stack.append([])
        elif m := END.match(line):
            if stack:
                stack.pop()
        elif m := DECL.match(line):
            prefix = ".".join(p for part in stack for p in part)
            starts.append((n, m, prefix))
    # a declaration runs to the line before the next top-level line that is not part of it
    toplevel = [n for n, line in enumerate(lines, start=1) if line[:1] not in (" ", "\t", "")]
    for (n, m, prefix) in starts:
        first = doc_start(lines, n)
        nxt = [t for t in toplevel if t > n and not lines[t - 1].startswith(("|", ")", "]", "}"))]
        stop = len(lines)
        for t in nxt:
            text = lines[t - 1]
            if text.startswith(("termination_by", "decreasing_by", "where")):
                continue
            stop = t - 1
            break
        first, last = trim(lines, first, stop)
        # a doc comment directly above belongs to the declaration; one above that is another's
        name = m.group("name")
        full = f"{prefix}.{name}" if prefix else name
        kind = m.group("kw")
        private = "private" in m.group("mods")
        span = Span(rel, module, first, last, full, kind, statement(lines, n, last, kind), private=private)
        lf.decls[full] = span
        if kind == "structure":
            header_end = next(k for k in range(n, last + 1) if lines[k - 1].rstrip().endswith("where"))
            lf.targets[full] = Span(rel, module, first, header_end, full, kind,
                                    "\n".join(lines[n - 1:header_end]), private=private, part="header")
            fields: list[tuple[int, int, str]] = []   # (start incl. doc, field line, name)
            pending = None
            k = header_end + 1
            while k <= last:
                text = lines[k - 1]
                if text.strip().startswith("/--"):
                    pending = k
                    while not lines[k - 1].rstrip().endswith("-/"):
                        k += 1
                elif fm := FIELD.match(text):
                    fields.append((pending or k, k, fm.group(1)))
                    pending = None
                k += 1
            for i, (start, at, fname) in enumerate(fields):
                stop_f = (fields[i + 1][0] - 1) if i + 1 < len(fields) else last
                a, b = trim(lines, start, stop_f)
                lf.targets[f"{full}.{fname}"] = Span(rel, module, a, b, f"{full}.{fname}", "field",
                                                     "\n".join(lines[at - 1:b]), part="field")
        else:
            lf.targets[full] = span
            # lines `field := value` of a definition written with `where`
            for k in range(n, last + 1):
                if wm := WHERE_FIELD.match(lines[k - 1]):
                    lf.targets[f"{full}@{wm.group(1)}"] = Span(rel, module, k, k, full, kind, lines[k - 1].strip(), part="line")
    # structural lines: every run outside the declarations
    inside = set()
    for span in lf.decls.values():
        inside.update(range(span.first, span.last + 1))
    run: list[int] = []
    for n in range(1, len(lines) + 2):
        if n <= len(lines) and n not in inside:
            run.append(n)
            continue
        if run:
            a, b = trim(lines, run[0], run[-1])
            if not all(blank(lines[k - 1]) for k in range(a, b + 1)):
                head = next(lines[k - 1].strip() for k in range(a, b + 1) if not blank(lines[k - 1]))
                head = head.removeprefix("/-!").removeprefix("/-").strip() or head
                lf.frames.append(Span(rel, module, a, b, None, "module", "\n".join(lines[a - 1:min(b, a + 29)]),
                                      title=f"{module}: {head[:60]}"))
            run = []
    return lf


def library() -> dict[str, LeanFile]:
    files = sorted((ROOT / LIB).rglob("*.lean")) + [ROOT / f"{LIB}.lean"]
    return {lf.path: lf for lf in map(parse, files)}


def resolve(target: str, lib: dict[str, LeanFile]) -> list[Span]:
    if target.startswith("mod:"):
        rel = f"{LIB}.lean" if target == f"mod:{LIB}" else f"{LIB}/{target[4:]}.lean"
        if rel not in lib:
            raise KeyError(target)
        return lib[rel].frames
    full = f"{LIB}.{target}"
    for lf in lib.values():
        if full in lf.targets:
            return [lf.targets[full]]
    raise KeyError(target)


@dataclass
class Box:
    n: int
    page: int
    x: float      # pt from the left
    y: float      # pt from the bottom, baseline
    wd: float
    ht: float
    dp: float
    section: str
    title: str
    targets: list[str]


def read_boxes() -> list[Box]:
    boxes = []
    for line in LK.read_text(encoding="utf-8").splitlines():
        n, page, x, y, wd, ht, dp, section, title, targets = line.split("|", 9)
        pt = lambda v: float(v.removesuffix("pt"))
        boxes.append(Box(int(n), int(page), int(x) / SP_PER_PT, int(y) / SP_PER_PT, pt(wd), pt(ht), pt(dp),
                         section, title.strip(), [t.strip() for t in targets.split(",") if t.strip()]))
    return boxes


def page_sizes() -> dict[int, tuple[float, float]]:
    out = subprocess.run(["pdfinfo", "-f", "1", "-l", "999", str(PDF)], capture_output=True, text=True,
                         check=True).stdout
    sizes = {}
    for m in re.finditer(r"Page\s+(\d+) size:\s+([\d.]+) x ([\d.]+) pts", out):
        sizes[int(m.group(1))] = (float(m.group(2)), float(m.group(3)))
    return sizes


def rect(box: Box, size: tuple[float, float]) -> tuple[float, float, float, float]:
    """[x, y, width, height], normalized, origin at the top left."""
    w, h = size
    left, right = box.x - PAD, box.x + box.wd + PAD
    top, bottom = h - (box.y + box.ht + PAD), h - (box.y - box.dp - PAD)
    return (left / w, top / h, (right - left) / w, (bottom - top) / h)


def overlaps(boxes: list[Box], sizes) -> list[str]:
    problems = []
    by_page: dict[int, list[tuple[Box, tuple]]] = {}
    for b in boxes:
        by_page.setdefault(b.page, []).append((b, rect(b, sizes[b.page])))
    for page, items in by_page.items():
        for i, (a, ra) in enumerate(items):
            if ra[0] < 0 or ra[1] < 0 or ra[0] + ra[2] > 1 or ra[1] + ra[3] > 1:
                problems.append(f"box {a.n} ({a.targets[0]}) leaves page {page}")
            for b, rb in items[i + 1:]:
                if (ra[0] < rb[0] + rb[2] and rb[0] < ra[0] + ra[2]
                        and ra[1] < rb[1] + rb[3] and rb[1] < ra[1] + ra[3]):
                    problems.append(f"page {page}: box {a.n} ({','.join(a.targets)}) overlaps box {b.n} "
                                    f"({','.join(b.targets)})")
    return problems


def coverage(lib: dict[str, LeanFile], linked: list[Span]) -> list[str]:
    covered: dict[str, set[int]] = {p: set() for p in lib}
    for span in linked:
        covered[span.path].update(range(span.first, span.last + 1))
    missing = []
    for path, lf in sorted(lib.items()):
        lines = [n for n in range(1, len(lf.lines) + 1) if not blank(lf.lines[n - 1]) and n not in covered[path]]
        if lines:
            runs, start, prev = [], lines[0], lines[0]
            for n in lines[1:] + [None]:
                if n != (prev or 0) + 1:
                    runs.append(f"{start}" if start == prev else f"{start}-{prev}")
                    start = n
                prev = n
            missing.append(f"{path}: lines {', '.join(runs)}")
    return missing


def safe_name(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]", "-", text).lstrip(".")


def git(*args: str) -> bytes:
    return subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, check=True).stdout


def write(boxes: list[Box], resolved: dict[int, list[Span]], sizes, commit: str) -> int:
    raw = PDF.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    committed = hashlib.sha256(git("show", f"{commit}:guide/reading-guide.pdf")).hexdigest()
    if committed != digest:
        sys.exit(f"guide/reading-guide.pdf differs from the one at {commit}: commit it first")
    url = f"{RAW}/{commit}/guide/reading-guide.pdf"
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir()
    defaults = {
        "kind": "passage",
        "status": "formalized",
        "subject": {"type": "pdf", "uri": url, "sha256": digest,
                    "citation": {"type": "book", "URL": url, "id": SOURCE_ID, "title": SOURCE_TITLE},
                    "extensions": {NS: {"bytes": len(raw), "physical_page_count": len(sizes),
                                        "source_id": SOURCE_ID}}},
        "object": {"type": "lean", "uri": REPO, "version": commit,
                   "extensions": {NS: {"destination": {"resolution": "exact"}}}},
        "extensions": {NS: {"provenance": {"actor": "author", "confirmed_by_human": False,
                                           "method": "curation"}}},
    }
    dump = lambda value: json.dumps(value, ensure_ascii=False, indent=2) + "\n"
    (OUT / "_defaults.json").write_text(dump(defaults), encoding="utf-8")
    count = 0
    for box in boxes:
        spans = resolved[box.n]
        item = f"guide-{box.n:03d}"
        title = box.title or default_title(box.targets[0])
        subject = {"location": {"page": box.page, "rect": [round(v, 6) for v in rect(box, sizes[box.page])]},
                   "title": title, "extensions": {NS: {"region": f"p{box.page:03d}-b{box.n:03d}"}}}
        folder = OUT / (box.section if box.section not in ("", "0") else "other")
        if len(spans) > 1:
            folder = folder / f"{item}-{safe_name(title)[:60]}"
        folder.mkdir(parents=True, exist_ok=True)
        for span in spans:
            location = {"module": span.module, "lines": [span.first, span.last]}
            ext: dict = {"destination": {"href": f"{REPO}/blob/{commit}/{span.path}",
                                         "fragment": f"L{span.first}" if span.first == span.last
                                         else f"L{span.first}-L{span.last}"},
                         "snippet": {"line": span.first, "text": span.snippet}}
            end = {"location": location, "role": "key"}
            if span.name:
                location = {"declaration": span.name, **location}
                end["location"] = location
                ext["declaration"] = {"id": span.name, "kind": span.kind,
                                      **({"private": True} if span.private else {})}
            else:
                end["title"] = span.title
            end["extensions"] = {NS: ext}
            record = {"id": item, "subject": [subject], "object": [end],
                      "extensions": {NS: {"locator": {"physical": [box.page], "printed": [box.page]}}}}
            label = span.name or f"{span.module}-L{span.first}-{span.last}"
            if span.part == "line":
                label = f"{label}-L{span.first}"
            stem = f"key__{safe_name(label)}"
            name = (f"{stem}.json" if len(spans) > 1 else f"{item}__{stem}.json")
            path = folder / name
            k = 2
            while path.exists():
                path = folder / name.replace(".json", f"-{k}.json")
                k += 1
            path.write_text(dump(record), encoding="utf-8")
            count += 1
    return count


def default_title(target: str) -> str:
    if target.startswith("mod:"):
        return f"module {target[4:]}"
    if "@" in target:
        name, fld = target.split("@", 1)
        return f"{name.split('.')[-1]}: {fld}"
    return target.split(".")[-1].replace("_", " ")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--commit", help="the commit that holds the PDF; the Lean links point into it")
    ap.add_argument("--check", action="store_true", help="resolve and check only; write nothing")
    args = ap.parse_args()
    if not args.check and not args.commit:
        ap.error("give --commit, or --check")
    lib = library()
    boxes = read_boxes()
    sizes = page_sizes()
    problems: list[str] = []
    resolved: dict[int, list[Span]] = {}
    for box in boxes:
        spans: list[Span] = []
        for target in box.targets:
            try:
                spans += resolve(target, lib)
            except KeyError:
                problems.append(f"box {box.n} (page {box.page}): no Lean target {target!r}")
        if not spans:
            problems.append(f"box {box.n} (page {box.page}) links nothing")
        resolved[box.n] = spans
        if box.page not in sizes:
            problems.append(f"box {box.n}: page {box.page} is not in {PDF.name}")
    problems += overlaps(boxes, sizes)
    linked = [s for spans in resolved.values() for s in spans]
    missing = coverage(lib, linked)
    total = sum(len(lf.lines) for lf in lib.values())
    nonblank = sum(1 for lf in lib.values() for line in lf.lines if not blank(line))
    decls = sum(len(lf.decls) for lf in lib.values())
    fields = sum(1 for lf in lib.values() for s in lf.targets.values() if s.kind == "field")
    print(f"{len(boxes)} boxes on {len(sizes)} pages; {len(linked)} links to {len(lib)} Lean files "
          f"({total} lines, {nonblank} non-blank; {decls} declarations, {fields} structure fields)")
    if problems or missing:
        for p in problems:
            print("problem:", p)
        for m in missing:
            print("not linked:", m)
        sys.exit(1)
    print("every non-blank line of the library is linked; no two boxes overlap")
    if not args.check:
        n = write(boxes, resolved, sizes, args.commit)
        print(f"wrote {n} annotation records into {OUT.relative_to(ROOT)}/")


if __name__ == "__main__":
    main()
