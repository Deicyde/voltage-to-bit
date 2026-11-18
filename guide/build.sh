#!/bin/sh
# Typeset the reading guide reproducibly and regenerate its locator files.
#
#   sh guide/build.sh
#
# The PDF's bytes depend only on the TeX file and the TeX installation: the
# timestamps are fixed and the trailer id is empty. The annotations pin the
# PDF's sha256, so a rebuild with another TeX installation needs a new export
# (README of this directory).
set -eu
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1762819200   # 2025-11-11 00:00:00 UTC, fixed
export FORCE_SOURCE_DATE=1
pdflatex -interaction=nonstopmode -halt-on-error reading-guide.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error reading-guide.tex >/dev/null
rm -f reading-guide.aux reading-guide.log reading-guide.out
python3 make_blueprint.py
shasum -a 256 reading-guide.pdf
