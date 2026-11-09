#!/bin/sh
# Workstream E: independent fresh rebuild of the frozen sources, WITHOUT writing
# into the frozen checkout and WITHOUT using its build products.
#
#   usage: [MODS="..."] fresh_rebuild.sh <frozen-checkout> <output-dir>
#
# Every module of the library is re-elaborated from source in dependency order
# with `lean -o`, into <output-dir>. LEAN_PATH contains <output-dir> and the
# dependency packages, but NOT <frozen-checkout>/.lake/build, so each module is
# checked against the freshly produced .olean files of its imports. Then
# scripts/Audit.lean is run against the fresh build, and each fresh .olean is
# compared byte-for-byte with the one in the frozen checkout.
set -eu
F="$(cd "$1" && pwd)"; OUT="$2"
mkdir -p "$OUT"
cd "$F"
FULL=$(lake env printenv LEAN_PATH)
# drop the frozen checkout's own build directory from LEAN_PATH
DEPS=$(printf '%s' "$FULL" | tr ':' '\n' | grep -v "^$F/.lake/build" | paste -sd ':' -)
export LEAN_PATH="$OUT:$DEPS"
# Module list in dependency order. Default: the 14 modules of commit 1880a36.
# For another commit pass the list in the environment variable MODS.
MODS="${MODS:-Model/PosSq Model/Device Model/Inverter Proofs/Reach Proofs/Margins Proofs/Guarantee Proofs/Existence Proofs/NonVacuity Proofs/Certificate Proofs/ModelError Proofs/Contamination Examples/IllustrativeDesign Examples/Illustrative Examples/NegativeControls}"
# every .lean file under VoltageToBit/ must be in the list above
N_SRC=$(find VoltageToBit -name '*.lean' | wc -l | tr -d ' ')
N_LIST=$(echo $MODS | wc -w | tr -d ' ')
echo "source files under VoltageToBit/: $N_SRC ; modules in rebuild list: $N_LIST"
[ "$N_SRC" = "$N_LIST" ] || { echo "MODULE LIST MISMATCH"; exit 1; }
for m in $MODS; do
  mkdir -p "$OUT/VoltageToBit/$(dirname "$m")"
  printf 'lean %-32s ' "VoltageToBit/$m.lean"
  lean -o "$OUT/VoltageToBit/$m.olean" "VoltageToBit/$m.lean" 2>&1 \
    | grep -v "designed for use with the module system" || true
  [ -f "$OUT/VoltageToBit/$m.olean" ] || { echo "FAILED: no olean"; exit 1; }
  echo ok
done
printf 'lean %-32s ' "VoltageToBit.lean"
lean -o "$OUT/VoltageToBit.olean" VoltageToBit.lean 2>&1 | grep -v "designed for use with the module system" || true
[ -f "$OUT/VoltageToBit.olean" ] && echo ok
echo "== axiom audit against the fresh build =="
lean scripts/Audit.lean 2>&1 | grep -v "designed for use with the module system" | head -n 4
echo "== byte comparison of fresh .olean files with the frozen checkout's =="
same=0; diff=0
for m in $MODS; do
  a=$(shasum -a 256 "$OUT/VoltageToBit/$m.olean" | cut -d' ' -f1)
  b=$(shasum -a 256 "$F/.lake/build/lib/lean/VoltageToBit/$m.olean" | cut -d' ' -f1)
  if [ "$a" = "$b" ]; then same=$((same+1)); else diff=$((diff+1)); echo "DIFFERENT: $m"; fi
done
echo "identical: $same   different: $diff"
