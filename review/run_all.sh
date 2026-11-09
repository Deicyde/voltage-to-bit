#!/bin/sh
# Workstream E: re-run every probe of the adversarial review.
#
#   usage: review/run_all.sh <frozen checkout> [--slow]
#
# <frozen checkout> is the read-only worktree at commit 1880a36. Nothing is
# written into it: Lean probes are compiled with `lake env lean` (no -o), and
# all outputs go to review/out/. Requires the checkout to be built already.
#
# --slow additionally runs the two long checks (about 10 minutes together):
#   * tooling/fresh_rebuild.sh : rebuild every module from source into a temp dir
#   * leanchecker              : replay every module of the frozen build in the kernel
set -u
F="$(cd "$1" && pwd)"; SLOW="${2:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="$HERE/out"; mkdir -p "$OUT"
filter() { /usr/bin/grep -v "designed for use with the module system"; }

echo "== frozen checkout: $(git --no-optional-locks -C "$F" rev-parse HEAD) =="
echo "tracked changes: $(git --no-optional-locks -C "$F" diff HEAD --stat | wc -l | tr -d ' ') ; untracked: $(git --no-optional-locks -C "$F" ls-files --others --exclude-standard | wc -l | tr -d ' ')"

echo "== Lean probes (each must print only standard axioms, no errors) =="
status=0
for p in P00_Smoke P01_JumpInputVacuity P02_RightContinuousStepExists P03_DeadlineBrackets \
         P04_ModelErrorScope P05_HypothesesAndDegeneracy P06_ExplicitRestatement \
         P07_LeanConventions P08_MiswiredUniversal; do
  (cd "$F" && lake env lean "$HERE/$p.lean" 2>&1 | filter) > "$OUT/$p.txt"
  if /usr/bin/grep -qE "error|sorryAx|warning" "$OUT/$p.txt"; then
    echo "FAIL  $p (see out/$p.txt)"; status=1
  else
    echo "ok    $p  ($(/usr/bin/grep -c "depends on axioms" "$OUT/$p.txt") axiom reports, all [propext, Classical.choice, Quot.sound]: $(if /usr/bin/grep "depends on axioms" "$OUT/$p.txt" | /usr/bin/grep -qv "\[propext, Classical.choice, Quot.sound\]"; then echo NO; else echo yes; fi))"
  fi
done

echo "== project audit script, run against the frozen build (output kept outside the checkout) =="
(cd "$F" && lake env lean scripts/Audit.lean 2>&1 | filter) > "$OUT/audit_frozen.txt"
head -n 3 "$OUT/audit_frozen.txt"
if diff -q "$OUT/audit_frozen.txt" "$F/evidence/lean/audit.txt" >/dev/null; then
  echo "identical to the committed evidence/lean/audit.txt"
else
  echo "DIFFERS from the committed evidence/lean/audit.txt"; status=1
fi

echo "== steps 1 and 2 of scripts/check.sh, read-only =="
(cd "$F" && python3 scripts/gen_design.py --check designs/illustrative-1v8.json \
  VoltageToBit/Examples/IllustrativeDesign.lean illustrative)
if (cd "$F" && /usr/bin/grep -rnE '\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^[[:space:]]*axiom[[:space:]]|@\[extern' VoltageToBit VoltageToBit.lean); then
  echo "FORBIDDEN TOKEN FOUND"; status=1
else echo "forbidden tokens: none found"; fi
echo "other meaning-changing constructs in the sources (set_option / instance / notation / macro / elab / run_cmd / attribute / local):"
(cd "$F" && /usr/bin/grep -rnE '^[[:space:]]*(set_option|instance|notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|run_cmd|run_elab|attribute|local|scoped|open .* in$)' VoltageToBit VoltageToBit.lean) || echo "  none"

echo "== environment inventory of the frozen build =="
(cd "$F" && lake env lean "$HERE/tooling/DumpDecls.lean" 2>&1 | filter) > "$OUT/decls_frozen.txt"
/usr/bin/grep "^## " "$OUT/decls_frozen.txt" | cut -c1-240

echo "== numeric probes =="
python3 "$HERE/num/n01_exact_numbers.py" "$F/designs/illustrative-1v8.json" > "$OUT/n01.txt"; tail -n 1 "$OUT/n01.txt"
python3 "$HERE/num/n02_device_and_margins.py" > "$OUT/n02.txt"; /usr/bin/grep -c " ok$" "$OUT/n02.txt" | sed 's/^/n02: margin inequalities without violation: /'
python3 "$HERE/num/n03_worst_case_delay.py" > "$OUT/n03.txt"; /usr/bin/grep "slowest trajectory" "$OUT/n03.txt"
python3 "$HERE/num/n04_adversarial_simulation.py" > "$OUT/n04.txt"; head -n 1 "$OUT/n04.txt"

echo "== tooling probes =="
TMP="$(mktemp -d)"
python3 "$HERE/tooling/gen_design_probe.py" "$F" "$TMP" > "$OUT/gen_design_probe.txt"; /usr/bin/grep -c "exit 0" "$OUT/gen_design_probe.txt" | sed 's/^/gen_design_probe: malformed inputs accepted by the generator: /'
TC="$(dirname "$(dirname "$(cd "$F" && lake env which lean)")")"
{
  echo "== 1. compile AuditGapDemo.lean =="
  (cd "$HERE/tooling" && "$TC/bin/lean" -o "$TMP/AuditGapDemo.olean" AuditGapDemo.lean 2>&1; echo "lean exit=$?")
  echo "== 2. token grep of scripts/check.sh applied to it =="
  if /usr/bin/grep -nE '\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^[[:space:]]*axiom[[:space:]]|@\[extern' "$HERE/tooling/AuditGapDemo.lean"; then echo "FORBIDDEN TOKEN FOUND"; else echo "none found"; fi
  echo "== 3. kernel replay with leanchecker =="
  LEAN_PATH="$TMP:$TC/lib/lean" "$TC/bin/leanchecker" AuditGapDemo 2>&1 | cut -c1-400; echo "(leanchecker rejects the file: see message above)"
} > "$OUT/audit_gap_demo.txt" 2>&1
/usr/bin/grep -E "does not depend|none found|leanchecker found" "$OUT/audit_gap_demo.txt"

if [ "$SLOW" = "--slow" ]; then
  echo "== slow: fresh rebuild from source =="
  "$HERE/tooling/fresh_rebuild.sh" "$F" "$TMP/fresh-build" > "$OUT/fresh_rebuild.txt" 2>&1
  /usr/bin/grep -E "AUDIT|declarations audited|MISMATCH|FAILED" "$OUT/fresh_rebuild.txt"
  FULL=$(cd "$F" && lake env printenv LEAN_PATH)
  DEPS=$(printf '%s' "$FULL" | tr ':' '\n' | /usr/bin/grep -v "^$F/.lake/build" | paste -sd ':' -)
  (cd "$F" && LEAN_PATH="$TMP/fresh-build:$DEPS" lean "$HERE/tooling/DumpDecls.lean" 2>&1 | filter) > "$OUT/decls_fresh.txt"
  if diff -q "$OUT/decls_frozen.txt" "$OUT/decls_fresh.txt" >/dev/null; then
    echo "fresh build and frozen build: identical declaration inventory (names, kinds, type hashes, value hashes)"
  else echo "fresh build DIFFERS from frozen build"; status=1; fi
  echo "== slow: kernel replay of the frozen build =="
  (cd "$F" && lake env "$TC/bin/leanchecker" VoltageToBit.Model.PosSq VoltageToBit.Model.Device \
     VoltageToBit.Model.Inverter VoltageToBit.Proofs.Reach VoltageToBit.Proofs.Margins \
     VoltageToBit.Proofs.Guarantee VoltageToBit.Proofs.Existence VoltageToBit.Proofs.NonVacuity \
     VoltageToBit.Proofs.Certificate VoltageToBit.Proofs.ModelError VoltageToBit.Proofs.Contamination \
     VoltageToBit.Examples.IllustrativeDesign VoltageToBit.Examples.Illustrative \
     VoltageToBit.Examples.NegativeControls VoltageToBit) > "$OUT/leanchecker.txt" 2>&1
  echo "leanchecker exit=$?" | tee -a "$OUT/leanchecker.txt"
fi
rm -rf "$TMP"
echo "== frozen checkout still clean: $(git --no-optional-locks -C "$F" status --porcelain | wc -l | tr -d ' ') changed paths =="
[ "$status" = 0 ] && echo "ALL REVIEW PROBES RAN AS RECORDED" || echo "SOME PROBE DID NOT BEHAVE AS RECORDED"
exit $status
