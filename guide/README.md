# voltage-to-bit: the specification and its proof

[`reading-guide.pdf`](reading-guide.pdf) (from [`reading-guide.tex`](reading-guide.tex))
states the library in equations and diagrams: the circuit and its square law,
the design record and the box, runs, the 26 checks, the deadlines and the
guarantee, a map of its proof, certificates, existence and uniqueness, other
models of the node, the supply-relative safe range, speed limits, two stages,
non-vacuity, the 1.8 V record and how tight its deadlines are, inputs that jump,
the negative controls, and a map of the modules.

The text names no Lean. In the annotated version every framed formula, symbol,
table cell and diagram node is linked to the exact Lean lines that state it: a
declaration, one field of a structure, one line of the 1.8 V record, or a
module's structural lines (imports, header comment, namespaces, section
comments). Together the links cover every non-blank line of the 23 Lean files of
the library, proofs included. It is published at
<https://deicyde.github.io/voltage-to-bit/pdf-overlay/viewer/index.html>
by `.github/workflows/pages.yml` on every push to `main`. It is a
[formal-companion](https://github.com/mathlib-initiative/formal-companion) PDF
overlay; the links are [Literature Links](https://github.com/mathlib-initiative/literature-links)
1.0.1 annotations in [`../annotations/`](../annotations/), and the viewer is in
[`../pdf-overlay/`](../pdf-overlay/).

To open it locally, from the repository root:

```sh
python3 pdf-overlay/tools/serve.py --build
```

and open the viewer address it prints. It fetches the PDF from the address in
this repository that the annotations name, and checks it against the sha256 they
pin; copying `guide/reading-guide.pdf` to
`.lake/overlay-pdf/voltage-to-bit-reading-guide.pdf` first avoids the download.

## How it is made

| File | Role |
| --- | --- |
| `reading-guide.tex` | the text; `\lk[title]{targets}{content}` typesets a linked piece and records, at shipout, its page and exact box, with its Lean targets, in `reading-guide.lk` |
| `reading-guide.lk` | those records, one line per box (committed: the annotations are generated from it) |
| `make_links.py` | resolves every target to Lean lines, checks that no two boxes overlap and that every non-blank line of the library is linked, and writes the annotations |
| `build.sh` | typesets the PDF reproducibly (two builds give the same bytes) and runs `make_links.py --check` |
| `make_site.py` | writes the landing page of the site, since this repository has no Verso site |

A target is a Lean name under the namespace `VoltageToBit` (a declaration from
its doc comment to its last line; for a structure, its doc comment and header),
`Struct.field` (one field with its doc comment), `Name@field` (the line
`field := …` of a definition written with `where`), or `mod:Path` (the
structural lines of `VoltageToBit/Path.lean`; `mod:VoltageToBit` is the root
file).

After a change to the text or to the Lean, regenerate everything with a clone of
formal-companion (`FC` below) and commit at each step, since the annotations pin
the PDF at a named commit:

```sh
sh guide/build.sh && git add guide && git commit -m "guide: ..."
python3 guide/make_links.py --commit "$(git rev-parse HEAD)"
python3 "$FC/scripts/cf.py" overlay sync . && python3 "$FC/scripts/cf.py" overlay check .
git add annotations pdf-overlay && git commit -m "Regenerate the overlay"
```

The text is typeset without `hyperref`, so that the PDF's own links do not
cover the overlay's boxes.

## Licence

The text, `reading-guide.tex` and `reading-guide.pdf`, is licensed under the
Creative Commons Attribution 4.0 International License ([`LICENSE`](LICENSE)); the PDF
states it under its title. That licence lets the overlay publish the PDF with its
site (`pdf.publish` in `pdf-overlay/overlay.config.json`). It covers the text only:
the rest of the repository has no licence yet.
