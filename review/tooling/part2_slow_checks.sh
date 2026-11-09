#!/bin/sh
# Workstream E, Part 2: the slow build-level checks for the second snapshot.
#   usage: part2_slow_checks.sh <frozen checkout at 9b13e95> <review dir> <scratch dir>
# Writes only into <review dir>/out2 and <scratch dir>.
set -u
F2="$(cd "$1" && pwd)"; HERE="$2"; TMP="$3"
OUT="$HERE/out2"; mkdir -p "$OUT" "$TMP"
MODS2="Model/PosSq Model/Device Model/Inverter Proofs/Reach Proofs/Margins Proofs/Guarantee Proofs/Existence Proofs/Concat Proofs/AtSupply Proofs/NonVacuity Proofs/Certificate Proofs/ModelError Proofs/Contamination Proofs/Chain Examples/IllustrativeDesign Examples/Illustrative Examples/NegativeControls"
filter() { /usr/bin/grep -v "designed for use with the module system"; }
echo "== fresh rebuild of 9b13e95 from source =="
MODS="$MODS2" "$HERE/tooling/fresh_rebuild.sh" "$F2" "$TMP/fresh-build-2" > "$OUT/fresh_rebuild.txt" 2>&1
/usr/bin/grep -E "source files|AUDIT|declarations audited|MISMATCH|FAILED" "$OUT/fresh_rebuild.txt"
(cd "$F2" && lake env lean "$HERE/tooling/DumpDecls.lean" 2>&1 | filter) > "$OUT/decls_frozen.txt"
FULL=$(cd "$F2" && lake env printenv LEAN_PATH)
DEPS=$(printf '%s' "$FULL" | tr ':' '\n' | /usr/bin/grep -v "^$F2/.lake/build" | paste -sd ':' -)
(cd "$F2" && LEAN_PATH="$TMP/fresh-build-2:$DEPS" lean "$HERE/tooling/DumpDecls.lean" 2>&1 | filter) > "$OUT/decls_fresh.txt"
if diff -q "$OUT/decls_frozen.txt" "$OUT/decls_fresh.txt" >/dev/null; then
  echo "fresh build and frozen build: identical declaration inventory ($(/usr/bin/grep -vc '^## ' "$OUT/decls_frozen.txt") constants)"
else echo "fresh build DIFFERS from frozen build"; fi
/usr/bin/grep "^## " "$OUT/decls_frozen.txt" | cut -c1-200 | head -3
echo "== project audit against the frozen build =="
(cd "$F2" && lake env lean scripts/Audit.lean 2>&1 | filter) > "$OUT/audit_frozen.txt"
head -n 3 "$OUT/audit_frozen.txt"
if diff -q "$OUT/audit_frozen.txt" "$F2/evidence/lean/audit.txt" >/dev/null; then echo "identical to the committed evidence/lean/audit.txt"; else echo "DIFFERS from the committed evidence/lean/audit.txt"; fi
echo "== kernel replay of the frozen build (leanchecker) =="
TC="$(dirname "$(dirname "$(cd "$F2" && lake env which lean)")")"
MODNAMES="$(echo $MODS2 | tr ' ' '\n' | sed 's#/#.#; s#^#VoltageToBit.#' | tr '\n' ' ') VoltageToBit"
(cd "$F2" && lake env "$TC/bin/leanchecker" $MODNAMES) > "$OUT/leanchecker.txt" 2>&1
echo "leanchecker exit=$?" | tee -a "$OUT/leanchecker.txt"
echo "== checkout still clean: $(git --no-optional-locks -C "$F2" status --porcelain | wc -l | tr -d ' ') changed paths =="
