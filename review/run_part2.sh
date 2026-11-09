#!/bin/sh
# Workstream E: re-run every probe of Part 2 of the adversarial review
# (delta 1880a36..9b13e95).
#
#   usage: review/run_part2.sh <frozen checkout at 9b13e95> [--slow]
#
# Nothing is written into the checkout. Outputs go to review/out2/.
# --slow additionally runs tooling/part2_slow_checks.sh (fresh rebuild from
# source, declaration inventory comparison, project audit, kernel replay;
# about 12 minutes).
set -u
F2="$(cd "$1" && pwd)"; SLOW="${2:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="$HERE/out2"; mkdir -p "$OUT"
filter() { /usr/bin/grep -v "designed for use with the module system"; }
echo "== frozen checkout: $(git --no-optional-locks -C "$F2" rev-parse HEAD) =="
echo "== Lean probes against 9b13e95 =="
status=0
for p in D01_JumpInput_PerInstant D02_GeneralityAndSandwich D03_ExplicitWellPosedness \
         D04_AtSupply_Chain_Reverse D05_Part1Ports P07_LeanConventions P08_MiswiredUniversal; do
  (cd "$F2" && lake env lean "$HERE/$p.lean" 2>&1 | filter) > "$OUT/$p.txt"
  if /usr/bin/grep -qE "error|sorryAx|warning" "$OUT/$p.txt"; then
    echo "FAIL  $p (see out2/$p.txt)"; status=1
  else
    echo "ok    $p  ($(/usr/bin/grep -c "depends on axioms" "$OUT/$p.txt") axiom reports, all standard: $(if /usr/bin/grep "depends on axioms" "$OUT/$p.txt" | /usr/bin/grep -qv "\[propext, Classical.choice, Quot.sound\]"; then echo NO; else echo yes; fi))"
  fi
done
echo "== sources: forbidden tokens and meaning-changing constructs =="
if (cd "$F2" && /usr/bin/grep -rnE '\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^[[:space:]]*axiom[[:space:]]|@\[extern' VoltageToBit VoltageToBit.lean); then
  echo "FORBIDDEN TOKEN FOUND"; status=1
else echo "forbidden tokens: none found"; fi
(cd "$F2" && /usr/bin/grep -rnE '^[[:space:]]*(set_option|instance|notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|run_cmd|run_elab|attribute|local|scoped|open .* in$)' VoltageToBit VoltageToBit.lean) || echo "set_option / instance / notation / macro / elab / run_cmd / attribute / local: none"
echo "== design record in sync =="
(cd "$F2" && python3 scripts/gen_design.py --check designs/illustrative-1v8.json \
  VoltageToBit/Examples/IllustrativeDesign.lean illustrative)
echo "== prose: quoted Lean names resolve =="
(cd "$F2" && lake env lean "$HERE/tooling/DocNames_9b13e95.lean" 2>&1 | filter) > "$OUT/doc_names.txt"
head -n 1 "$OUT/doc_names.txt"
echo "== prose: paths named in README.md =="
for p in docs/discrepancy-report.md docs/experiment-loop.md docs/adversarial-review.md experiments search; do
  if [ -e "$F2/$p" ]; then echo "exists   $p"; else echo "MISSING  $p (at this commit)"; fi
done
echo "== numeric probe =="
python3 "$HERE/num/n05_part2_numbers.py" > "$OUT/n05.txt"; /usr/bin/grep -E "^\(b\)|all six" "$OUT/n05.txt"
if [ "$SLOW" = "--slow" ]; then
  TMP="$(mktemp -d)"
  "$HERE/tooling/part2_slow_checks.sh" "$F2" "$HERE" "$TMP" | tee "$OUT/slow_checks.txt"
  rm -rf "$TMP"
fi
echo "== checkout still clean: $(git --no-optional-locks -C "$F2" status --porcelain | wc -l | tr -d ' ') changed paths =="
[ "$status" = 0 ] && echo "ALL PART 2 PROBES RAN AS RECORDED" || echo "SOME PROBE DID NOT BEHAVE AS RECORDED"
exit $status
