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
    "psq": ("path-a", "The positive part squared", ["VoltageToBit.psq"], []),
    "params": ("path-a", "The five device parameters", ["VoltageToBit.Params"], []),
    "currents": ("path-a", "The transistor currents",
                 ["VoltageToBit.In", "VoltageToBit.Ip", "VoltageToBit.Inet"], []),
    "design": ("path-a", "The design record", ["VoltageToBit.Design"], []),
    "box": ("path-a", "The parameter box", ["VoltageToBit.Design.InBox"], []),
    "safe": ("path-a", "The safe voltage domain", ["VoltageToBit.Design.Safe"], []),
    "trajectory": ("path-a", "Trajectories: the dynamics", ["VoltageToBit.IsTrajectory"], []),
    "record": ("path-a", "The illustrative record", ["VoltageToBit.Examples.illustrative"], []),
    "guarantee": ("path-a", "The theorem", ["VoltageToBit.Examples.illustrative_guarantee"], []),
    "admissible": ("path-b", "The arithmetic checks", ["VoltageToBit.Design.Admissible"], []),
    "margins": ("path-b", "The current margins",
                ["VoltageToBit.Design.Iup", "VoltageToBit.Design.Idn", "VoltageToBit.Design.RhiP",
                 "VoltageToBit.Design.RhiN", "VoltageToBit.Design.RloN", "VoltageToBit.Design.RloP"], []),
    "deadlines": ("path-b", "The two deadlines",
                  ["VoltageToBit.Design.tauUp", "VoltageToBit.Design.tauDn"], []),
    "decoding": ("path-b", "Decoding to bits",
                 ["VoltageToBit.decode", "VoltageToBit.Design.decodeIn",
                  "VoltageToBit.Design.decodeOut", "VoltageToBit.Design.tau"], []),
    "general": ("path-b", "The four general statements",
                ["VoltageToBit.IsTrajectory.safe", "VoltageToBit.IsTrajectory.rise",
                 "VoltageToBit.IsTrajectory.fall", "VoltageToBit.IsTrajectory.decoded"], []),
    "admissible-instance": ("instances", "The record passes the checks",
                            ["VoltageToBit.Examples.illustrative_admissible"], []),
    "existence": ("instances", "Runs exist",
                  ["VoltageToBit.exists_trajectory", "VoltageToBit.Examples.illustrative_scenario"],
                  ["VoltageToBit.Examples.nominal", "VoltageToBit.Examples.uRamp",
                   "VoltageToBit.Examples.wSin"]),
    "brackets": ("instances", "How tight the deadlines are",
                 ["VoltageToBit.Examples.rise_deadline_bracket",
                  "VoltageToBit.Examples.fall_deadline_bracket"], []),
    "steps": ("instances", "Where the theorem says nothing",
              ["VoltageToBit.Examples.stepL_no_trajectory", "VoltageToBit.Examples.step_input_scope"],
              ["VoltageToBit.Examples.uStepL", "VoltageToBit.Examples.uStepR"]),
}

MARK = re.compile(r"^% @(passage|end) ([a-z0-9-]+)\s*$")
SUBSECTION = re.compile(r"\\subsection\{([^}]*)\}")


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
        "A passage of the reading guide and the declarations it describes.",
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
    out = ["# Locators for the reading guide", "",
           f"Line ranges refer to `{TEX.name}` in `guide/` (SHA-256 `{digest}`).",
           "Each section is one passage of the guide, generated by `guide/make_blueprint.py`.", ""]
    for ident, (group, heading, key, support) in PASSAGES.items():
        first, last = found[ident]
        text = "\n".join(lines[first - 1:last])
        sub = SUBSECTION.search(text)
        if not sub or sub.group(1) != heading:
            sys.exit(f"passage {ident}: its heading in {TEX.name} is not {heading!r}")
        out += [f"## {heading}", "", f"Lines {first}-{last}: the passage of the guide on {heading.lower()}.", ""]
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
