# What voltage-to-bit specifies

[`reading-guide.pdf`](reading-guide.pdf) (from [`reading-guide.tex`](reading-guide.tex))
states the specification in plain words: the circuit and its transistor law, what
is uncertain, how the output may move, how voltages are read as bits, the
arithmetic checks a design must pass, the deadlines, the guarantee, the concrete
1.8 V inverter, how tight its deadlines are, why runs exist, what another model
of the node must satisfy, and what is not claimed.

The text names no Lean. The annotated version links each passage to the Lean that
states it: select a passage and the declarations appear beside it, with their
statements and links to the source. It is published at
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
| `reading-guide.tex` | the text; each passage is marked by `% @passage <id>` and `% @end <id>` |
| `make_blueprint.py` | the table of passages and the declarations each one is linked to; writes `blueprint/sources/reading-guide-locators.md` (line ranges and the TeX file's sha256) and one roadmap page per passage under `blueprint/roadmap/` |
| `build.sh` | typesets the PDF reproducibly (two builds give the same bytes) and runs `make_blueprint.py` |
| `make_site.py` | writes the landing page of the site, since this repository has no Verso site |

After a change to the text, regenerate everything with a clone of
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
  --source-title "What voltage-to-bit specifies" --page-offset 0
python3 "$FC/scripts/cf.py" overlay sync . && python3 "$FC/scripts/cf.py" overlay check .
git add annotations pdf-overlay && git commit -m "Regenerate the overlay"
```

The text is typeset without `hyperref`: `pdftotext -bbox-layout` of poppler
26.04.0, which the export uses, aborts on a PDF built with it.

## Licence

The text, `reading-guide.tex` and `reading-guide.pdf`, is licensed under the
Creative Commons Attribution 4.0 International License ([`LICENSE`](LICENSE)); the PDF
states it under its title. That licence lets the overlay publish the PDF with its
site (`pdf.publish` in `pdf-overlay/overlay.config.json`). It covers the text only:
the rest of the repository has no licence yet.
