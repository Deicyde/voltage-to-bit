#!/bin/sh
# Reproduce every formal check of this repository.
#
#   scripts/check.sh           incremental build, then all checks
#   scripts/check.sh --fresh   delete this project's own build products first,
#                              so every file of this project is recompiled
#                              (Mathlib's prebuilt binaries are kept)
#
# What this establishes: the Lean kernel accepted every declaration in this
# build, none of them depends on an axiom beyond propext / Classical.choice /
# Quot.sound, and the Lean design records match the JSON design files.
# What it does not establish: that the statements mean what the prose says
# (read them), or that any physical device obeys the model.
set -eu
cd "$(dirname "$0")/.."

if [ "${1:-}" = "--fresh" ]; then
  echo "== 0. removing this project's build products =="
  rm -rf .lake/build
fi

echo "== 1. design records in sync with JSON =="
python3 scripts/gen_design.py --check designs/illustrative-1v8.json \
  VoltageToBit/Examples/IllustrativeDesign.lean illustrative
if [ -x scripts/check_generated.sh ]; then scripts/check_generated.sh; fi

echo "== 2. forbidden tokens in the Lean sources =="
if grep -rnE '\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^[[:space:]]*axiom[[:space:]]|@\[extern' \
    VoltageToBit VoltageToBit.lean; then
  echo "FORBIDDEN TOKEN FOUND"
  exit 1
fi
echo "none found"

echo "== 3. build =="
lake build 2>&1 | grep -v "designed for use with the module system" | tail -n 5

echo "== 4. axiom audit over every declaration =="
mkdir -p evidence/lean
lake env lean scripts/Audit.lean 2>&1 | grep -v "designed for use with the module system" \
  | tee evidence/lean/audit.txt
grep -q "AUDIT OK" evidence/lean/audit.txt

echo "== versions =="
{
  lean --version
  lake --version
  echo "mathlib rev: $(sed -n 's/.*"rev": "\([0-9a-f]*\)".*/\1/p' lake-manifest.json | head -n 1)"
} | tee evidence/lean/versions.txt

echo "ALL FORMAL CHECKS PASSED"
