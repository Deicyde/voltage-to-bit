#!/bin/sh
# Typeset the guide reproducibly and check its links.
#
#   sh guide/build.sh
#
# The PDF's bytes depend only on the TeX file and the TeX installation: the
# timestamps are fixed and the trailer id is empty. pdfTeX also writes
# reading-guide.lk, the page and exact box of every linked formula, symbol and
# node; make_links.py --check resolves each box's Lean targets and fails unless
# no two boxes overlap and every non-blank line of the library is linked.
set -eu
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1762819200   # 2025-11-11 00:00:00 UTC, fixed
export FORCE_SOURCE_DATE=1
pdflatex -interaction=nonstopmode -halt-on-error reading-guide.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error reading-guide.tex >/dev/null
rm -f reading-guide.aux reading-guide.log reading-guide.out
python3 make_links.py --check
shasum -a 256 reading-guide.pdf
