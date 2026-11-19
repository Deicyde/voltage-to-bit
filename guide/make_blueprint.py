#!/usr/bin/env python3
"""Write the roadmap-locators files of the reading guide from its TeX source.

formal-companion's `cf export roadmap-locators` (docs/exporters.md section 9 of
that repository) reads two kinds of Markdown file under `guide/blueprint/`:

- `sources/reading-guide-locators.md`: one section per passage of the guide,
  giving the passage's line range in `reading-guide.tex` and the file's sha256;
- `roadmap/<group>/<passage>.md`: one page per passage, whose front matter names
  the Lean declarations the passage describes and whose `## Sources` section
  links to the passage's locator section.

The passages are marked in the TeX file by the comments `% @passage <id>` and
`% @end <id>`; the line range of a passage is the lines strictly between them.
The declarations of each passage are listed in PASSAGES below. Run this after
every change of the TeX file, so that line ranges and the pinned sha256 follow it:

    python3 guide/make_blueprint.py
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = HERE / "reading-guide.tex"
BLUEPRINT = HERE / "blueprint"
LOCATORS = BLUEPRINT / "sources" / "reading-guide-locators.md"

# id: (group, heading, key declarations, supporting declarations)
PASSAGES: dict[str, tuple[str, str, list[str], list[str]]] = {
    "circuit": ("model", "The circuit and its transistors",
                ["VoltageToBit.psq", "VoltageToBit.Params", "VoltageToBit.In", "VoltageToBit.Ip",
                 "VoltageToBit.Inet"], []),
    "uncertainty": ("model", "What is uncertain",
                    ["VoltageToBit.Design", "VoltageToBit.Design.InBox"], []),
    "dynamics": ("model", "How the output may move",
                 ["VoltageToBit.IsTrajectory", "VoltageToBit.Design.Safe"], []),
    "bits": ("model", "Reading bits",
             ["VoltageToBit.decode", "VoltageToBit.Design.decodeIn", "VoltageToBit.Design.decodeOut"], []),
    "checks": ("theorem", "The arithmetic checks",
               ["VoltageToBit.Design.Admissible"],
               ["VoltageToBit.Design.Iup", "VoltageToBit.Design.Idn", "VoltageToBit.Design.RhiP",
                "VoltageToBit.Design.RhiN", "VoltageToBit.Design.RloN", "VoltageToBit.Design.RloP"]),
    "deadlines": ("theorem", "The deadlines",
                  ["VoltageToBit.Design.tauUp", "VoltageToBit.Design.tauDn"], ["VoltageToBit.Design.tau"]),
    "guarantee": ("theorem", "The guarantee",
                  ["VoltageToBit.IsTrajectory.safe", "VoltageToBit.IsTrajectory.rise",
                   "VoltageToBit.IsTrajectory.fall", "VoltageToBit.IsTrajectory.decoded"], []),
    "instance": ("instance", "A concrete inverter",
                 ["VoltageToBit.Examples.illustrative_guarantee", "VoltageToBit.Examples.illustrative",
                  "VoltageToBit.Examples.illustrative_admissible"], []),
    "tightness": ("instance", "How tight the deadlines are",
                  ["VoltageToBit.Examples.illustrative_guarantee_refined",
                   "VoltageToBit.Examples.rise_deadline_bracket",
                   "VoltageToBit.Examples.fall_deadline_bracket"], []),
    "existence": ("instance", "Runs exist",
                  ["VoltageToBit.exists_trajectory", "VoltageToBit.exists_solution",
                   "VoltageToBit.solution_unique", "VoltageToBit.Examples.illustrative_scenario"], []),
    "models": ("scope", "Other models of the same node",
               ["VoltageToBit.IsTrajectory.of_sandwich", "VoltageToBit.IsTrajectory.of_static_sandwich",
                "VoltageToBit.IsTrajectory.of_charge_balance"], []),
    "limits": ("scope", "What is not claimed",
               ["VoltageToBit.Examples.stepL_no_trajectory", "VoltageToBit.Examples.step_input_scope"],
               ["VoltageToBit.Examples.uStepL", "VoltageToBit.Examples.uStepR"]),
}

MARK = re.compile(r"^% @(passage|end) ([a-z0-9-]+)\s*$")
SECTION = re.compile(r"\\(?:sub)?section\{([^}]*)\}")


def spans(lines: list[str]) -> dict[str, tuple[int, int]]:
    """The line range (1-based, inclusive) between each passage's two markers."""
    found: dict[str, tuple[int, int]] = {}
    open_id, start = None, 0
    for number, line in enumerate(lines, start=1):
        match = MARK.match(line)
        if not match:
            continue
        kind, ident = match.groups()
        if kind == "passage":
            if open_id is not None:
                sys.exit(f"line {number}: passage {ident} opens inside {open_id}")
            open_id, start = ident, number + 1
        else:
            if ident != open_id:
                sys.exit(f"line {number}: end of {ident}, but {open_id} is open")
            found[ident] = (start, number - 1)
            open_id = None
    if open_id is not None:
        sys.exit(f"passage {open_id} is not closed")
    return found


def page(heading: str, names: list[str], origin: str, anchor: str) -> str:
    return "\n".join([
        "---",
        "declaration: definition-or-theorem",
        f"origin: {origin}",
        "statement: formalized",
        f"lean: {', '.join(names)}",
        "---",
        "",
        f"# {heading}",
        "",
        "A passage of the specification in plain words, and the Lean that states it.",
        "",
        "## Sources",
        "",
        f"- [{heading}](../../sources/reading-guide-locators.md#{anchor})",
        "",
    ])


def main() -> None:
    raw = TEX.read_bytes()
    lines = raw.decode("utf-8").split("\n")
    found = spans(lines)
    missing = sorted(set(PASSAGES) - set(found))
    if missing:
        sys.exit(f"passages listed here but not marked in {TEX.name}: {', '.join(missing)}")
    digest = hashlib.sha256(raw).hexdigest()
    out = ["# Locators for the specification in plain words", "",
           f"Line ranges refer to `{TEX.name}` in `guide/` (SHA-256 `{digest}`).",
           "Each section is one passage of the guide, generated by `guide/make_blueprint.py`.", ""]
    for ident, (group, heading, key, support) in PASSAGES.items():
        first, last = found[ident]
        text = "\n".join(lines[first - 1:last])
        sub = SECTION.search(text)
        if not sub or sub.group(1) != heading:
            sys.exit(f"passage {ident}: its heading in {TEX.name} is not {heading!r}")
        out += [f"## {heading}", "", f"Lines {first}-{last}: {heading.lower()}.", ""]
    LOCATORS.parent.mkdir(parents=True, exist_ok=True)
    LOCATORS.write_text("\n".join(out), encoding="utf-8")
    roadmap = BLUEPRINT / "roadmap"
    for ident, (group, heading, key, support) in PASSAGES.items():
        anchor = re.sub(r"-+", "-", re.sub(r"[^a-z0-9]+", "-", heading.lower())).strip("-")
        folder = roadmap / group
        folder.mkdir(parents=True, exist_ok=True)
        (folder / f"{ident}.md").write_text(page(heading, key, "cited", anchor), encoding="utf-8")
        if support:
            (folder / f"{ident}-support.md").write_text(page(heading, support, "bridged", anchor),
                                                         encoding="utf-8")
    for name in ("README.md",):
        for folder in (BLUEPRINT, BLUEPRINT / "sources", roadmap):
            target = folder / name
            if not target.exists():
                target.write_text(f"# {folder.name}\n\nGenerated by `guide/make_blueprint.py`.\n",
                                  encoding="utf-8")
    print(f"{len(PASSAGES)} passages; TeX sha256 {digest}")


if __name__ == "__main__":
    main()
