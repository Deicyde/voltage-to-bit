# Reading guide of the trusted specification

[`reading-guide.tex`](reading-guide.tex) (typeset as
[`reading-guide.pdf`](reading-guide.pdf), 5 pages) lists exactly what a reader
has to read to trust the theorems of this repository: the definitions and
statements, file by file and line by line, with what each says and what to check.

| Section | What it covers | Lean to read |
| --- | --- | --- |
| 2, path A | the theorem about the illustrative 1.8 V record, `Examples.illustrative_guarantee` | about 80 lines |
| 3, path B | the theorem about every admissible record, `IsTrajectory.safe`, `.rise`, `.fall`, `.decoded` | about 120 lines in all |
| 4 | statements that show the hypotheses can be met | four groups of statements |
| 5, 6 | what Lean and Mathlib supply; what can be skipped | none |

## The annotated guide

The same PDF with each passage boxed and, beside it, the Lean declarations the
passage names, each with its statement and a link to its line on GitHub. It is a
[formal-companion](https://github.com/mathlib-initiative/formal-companion) PDF
overlay: 18 passages, 40 links, stored as
[Literature Links](https://github.com/mathlib-initiative/literature-links) 1.0.1
annotations in [`../annotations/`](../annotations/), with the viewer in
[`../pdf-overlay/`](../pdf-overlay/).

To open it, from the repository root:

```sh
mkdir -p .lake/overlay-pdf && cp guide/reading-guide.pdf .lake/overlay-pdf/voltage-to-bit-reading-guide.pdf
python3 pdf-overlay/tools/serve.py --build
```

and open the viewer address it prints (`/pdf-overlay/viewer/index.html`). The
first line puts the PDF into the viewer's cache. The annotations name the PDF's
address in this repository on GitHub, which needs a login while the repository
is private, so the server cannot fetch it there itself; it checks the cached
file against the sha256 the annotations pin.

## How it is made

| File | Role |
| --- | --- |
| `reading-guide.tex` | the guide; each passage is marked by `% @passage <id>` and `% @end <id>` |
| `build.sh` | typesets the PDF reproducibly (two builds give the same bytes) and runs `make_blueprint.py` |
| `make_blueprint.py` | lists the declarations of each passage, and writes `blueprint/sources/reading-guide-locators.md` (line ranges and the TeX file's sha256) and one page per passage under `blueprint/roadmap/` |
| `make_site.py` | writes the landing page of the local site, since this repository has no Verso site |

After a change to the guide, regenerate everything with a clone of
formal-companion (`FC` below) and commit at each step, since the export reads a
clean checkout at a named commit:

```sh
sh guide/build.sh && git add guide && git commit -m "guide: ..."
C=$(git rev-parse HEAD)
python3 "$FC/scripts/cf.py" overlay export . --convention roadmap-locators --commit "$C" -- \
  --pdf guide/reading-guide.pdf \
  --pdf-url "https://raw.githubusercontent.com/Deicyde/voltage-to-bit/$C/guide/reading-guide.pdf" \
  --tex guide/reading-guide.tex --blueprint guide/blueprint \
  --source-id voltage-to-bit-reading-guide \
  --source-title "Reading the trusted specification of voltage-to-bit" --page-offset 0
python3 "$FC/scripts/cf.py" overlay sync . && python3 "$FC/scripts/cf.py" overlay check .
git add annotations pdf-overlay && git commit -m "Regenerate the overlay of the reading guide"
```

The guide is typeset without `hyperref`: `pdftotext -bbox-layout` of poppler
26.04.0, which the export uses, aborts on a PDF built with it.

The guide is prose. Where it differs from the Lean, the Lean is right, and the
cards beside each passage show the Lean itself.
