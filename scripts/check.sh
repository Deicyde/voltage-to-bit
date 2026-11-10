#!/bin/sh
# Reproduce every formal check of this repository.
#
#   scripts/check.sh               all steps below except 9
#   scripts/check.sh --quick       steps 1 to 5 only: no kernel replay
#   scripts/check.sh --whole-env   all steps, including 9
#   --fresh        delete this project's own build products first, so every
#                  file of this project is recompiled (.lake/packages, the
#                  prebuilt Mathlib, is kept)
#   --keep-going   do not stop at the first failing step: run every step whose
#                  inputs exist and report each one
#
# Steps. Each prints one line "RESULT <step>: ok" or "RESULT <step>: FAILED".
#   1 design-record   the generated Lean design record matches its JSON file
#   2 source-scan     no construct in the library sources or in lakefile.toml
#                     that can bypass the kernel or change how later text is
#                     elaborated (scripts/lean_scan.py: a deny-list, a tripwire)
#   3 build           `lake build` exits with status 0
#   4 axiom-audit     no declaration of the library depends on an axiom beyond
#                     propext, Classical.choice, Quot.sound; the library
#                     declares no axiom, opaque or unsafe constant, instance
#                     or simp lemma of its own (scripts/Audit.lean)
#   5 import-closure  every .lean file of the library is a module of the
#                     audited environment, and the other way round
#   6 replay-modules  `leanchecker` re-checks, in Lean's kernel, the
#                     declarations stored in the compiled file of every module
#                     of the library, on top of that module's imports
#   7 export          `leanexport` writes every declaration of the library and
#                     everything those declarations depend on (the part of
#                     Mathlib and of Lean core that the library uses) to one
#                     file; scripts/export_census.py confirms that every
#                     declaration of the library is in it
#   8 replay-export   that file is checked from an empty environment by Lean's
#                     kernel (leanchecker, leanchecker-paranoid) and by four
#                     other checkers (lean4lean, nanoda, con-leche, con-ron);
#                     none of them reads a compiled file
#   9 whole-env       (--whole-env only) `leanchecker --fresh` re-checks, in
#                     Lean's kernel and from an empty environment, every
#                     declaration of every imported module, used by the
#                     library or not: all of the imported Mathlib and Lean core
#
# What a pass of steps 1 to 8 establishes: the declarations of this library,
# and every declaration of Mathlib and of Lean core that they depend on, are
# accepted, when replayed from an empty environment, by Lean's kernel and by
# the four other checkers of step 8; none of them depends on an axiom beyond
# the three named in step 4; the compiled files are up to date with the files
# on disk (Lake's own check, step 3) and every .lean file of the library is
# among them; and the Lean design record matches the JSON design file.
# What it does not establish: that the statements mean what the prose says
# (read them), or that any physical device obeys the model. The checkers of
# step 8 read what `leanexport` wrote, so its faithfulness to the compiled
# files is trusted; so is the Lean elaborator's reading of the source text.
# Without --whole-env, declarations of Mathlib that the library does not
# depend on are not re-checked; with it they are, by Lean's own kernel only.
#
# Records are written to evidence/lean/. They contain no dates or timings, so
# a second run on the same sources reproduces them byte for byte. --quick does
# not touch kernel-replay.txt.
#
# Time, measured on an 18 GB laptop that was busy with other work: about one
# minute for --quick, five minutes for the default, six more for --whole-env,
# plus the time to recompile with --fresh.
# Environment: CHECK_REPLAY_JOBS (default 2) is the number of modules
# `leanchecker` replays at a time in step 6; each needs about 2 GB of memory.
#
# Exit status: 0 every step that was run passed; 1 a step failed; 2 usage.
# The last line of output says which of the two happened and, on success,
# exactly what was replayed and by which tool, or that nothing was.
#
# Negative controls for this script: scripts/selftest.sh.
set -u
cd "$(dirname "$0")/.." || exit 2

FRESH=0; QUICK=0; WHOLE=0; KEEP=0
for arg in "$@"; do
  case "$arg" in
    --fresh) FRESH=1 ;;
    --quick) QUICK=1 ;;
    --whole-env) WHOLE=1 ;;
    --keep-going) KEEP=1 ;;
    -h|--help) sed -n '2,/^set -u/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    *) echo "check.sh: unknown option $arg (try --help)" >&2; exit 2 ;;
  esac
done
if [ "$QUICK" = 1 ] && [ "$WHOLE" = 1 ]; then
  echo "check.sh: --quick and --whole-env exclude each other" >&2; exit 2
fi

JOBS="${CHECK_REPLAY_JOBS:-2}"
DESIGN_JSON=designs/illustrative-1v8.json
DESIGN_LEAN=VoltageToBit/Examples/IllustrativeDesign.lean
DESIGN_NAME=illustrative
EVIDENCE=evidence/lean
STANDARD_AXIOMS='"propext", "Classical.choice", "Quot.sound"'

TMP="$(mktemp -d "${TMPDIR:-/tmp}/vtb-check.XXXXXX")" || exit 2
trap 'rm -rf "$TMP"' EXIT
trap 'exit 130' INT TERM
mkdir -p "$TMP/lists" "$EVIDENCE"

FAILED=""
REPLAYED=""          # what the last line reports

filter() { grep -v "designed for use with the module system" || true; }
indent() { sed 's/^/    /'; }
sha256_of() {
  python3 -c 'import hashlib, sys
h = hashlib.sha256()
with open(sys.argv[1], "rb") as f:
    for block in iter(lambda: f.read(1 << 20), b""):
        h.update(block)
print(h.hexdigest())' "$1"
}
count_lines() { wc -l <"$1" | tr -d ' '; }

last_line() {
  if [ -f "$TMP/kernel-replay.txt" ]; then
    {
      echo
      if [ -n "$FAILED" ]; then
        echo "Outcome of the run of scripts/check.sh that wrote this record: FAILED:$FAILED"
      else
        echo "Outcome of the run of scripts/check.sh that wrote this record: every step passed."
      fi
    } >>"$TMP/kernel-replay.txt"
    cp "$TMP/kernel-replay.txt" "$EVIDENCE/kernel-replay.txt"
    echo "record written to $EVIDENCE/kernel-replay.txt"
  fi
  if [ -n "$FAILED" ]; then
    echo "CHECK FAILED:$FAILED"
    exit 1
  fi
  if [ "$QUICK" = 1 ]; then
    echo "QUICK CHECK PASSED (steps 1 to 5). THE KERNEL REPLAY WAS SKIPPED (--quick): no declaration was re-checked by any kernel in this run."
  else
    echo "ALL FORMAL CHECKS PASSED. Kernel replay: $REPLAYED"
  fi
  exit 0
}
ok() { echo "RESULT $1: ok${2:+ ($2)}"; }
fail() {
  echo "RESULT $1: FAILED ($2)"
  FAILED="$FAILED $1"
  if [ "$KEEP" = 0 ]; then last_line; fi
}
# failed <step>: has this step, or a step whose name starts with it, failed?
failed() { case " $FAILED " in *" $1"*) return 0 ;; *) return 1 ;; esac; }

if [ "$FRESH" = 1 ]; then
  echo "== 0. removing this project's build products =="
  rm -rf .lake/build
fi

# ---------------------------------------------------------------------------
echo "== 1. design record in sync with its JSON file =="
if python3 scripts/gen_design.py --check "$DESIGN_JSON" "$DESIGN_LEAN" "$DESIGN_NAME"; then
  ok design-record
else
  fail design-record "$DESIGN_LEAN is stale or $DESIGN_JSON was rejected; see the message above"
fi

# ---------------------------------------------------------------------------
echo "== 2. forbidden constructs in the library sources and in lakefile.toml =="
python3 scripts/lean_scan.py --lakefile lakefile.toml VoltageToBit.lean VoltageToBit >"$TMP/scan.txt" 2>&1
status=$?
cat "$TMP/scan.txt"
cp "$TMP/scan.txt" "$EVIDENCE/source-scan.txt"
if [ "$status" = 0 ]; then ok source-scan; else fail source-scan "see the findings above"; fi

# ---------------------------------------------------------------------------
echo "== 3. build =="
lake build >"$TMP/build.log" 2>&1
status=$?
if [ "$status" = 0 ]; then
  filter <"$TMP/build.log" | tail -n 3
  ok build
else
  filter <"$TMP/build.log" | cut -c1-600 | tail -n 60
  fail build "lake build exited with status $status"
fi

# ---------------------------------------------------------------------------
echo "== 4. axiom audit over every declaration of the library =="
if failed build; then
  echo "not run: the build failed"
  fail axiom-audit "not run: the build failed"
else
  VTB_AUDIT_LISTS="$TMP/lists" lake env lean scripts/Audit.lean >"$TMP/audit.log" 2>&1
  status=$?
  filter <"$TMP/audit.log" >"$EVIDENCE/audit.txt"
  sed '/^theorems with a name of their own/,$d' "$EVIDENCE/audit.txt" | cut -c1-2000
  if [ "$status" = 0 ] && grep -q "^AUDIT OK" "$EVIDENCE/audit.txt"; then
    grep "^theorems with a name of their own" "$EVIDENCE/audit.txt" | sed "s|:\$| are listed in $EVIDENCE/audit.txt|"
    ok axiom-audit
  else
    fail axiom-audit "lean exited with status $status; see the output above"
  fi
fi

# ---------------------------------------------------------------------------
echo "== 5. every source file is a module of the audited environment =="
if [ ! -f "$TMP/lists/modules.txt" ]; then
  echo "not run: the audit did not produce a list of modules"
  fail import-closure "not run: no list of modules"
else
  { [ -f VoltageToBit.lean ] && echo VoltageToBit
    find VoltageToBit -name '*.lean' | sed 's/\.lean$//; s#/#.#g'
  } | LC_ALL=C sort >"$TMP/source-modules.txt"
  LC_ALL=C sort "$TMP/lists/modules.txt" >"$TMP/env-modules.txt"
  n_src="$(count_lines "$TMP/source-modules.txt")"
  n_env="$(count_lines "$TMP/env-modules.txt")"
  echo "source files of the library (VoltageToBit.lean and VoltageToBit/**/*.lean): $n_src"
  echo "modules of the library in the audited environment: $n_env"
  if cmp -s "$TMP/source-modules.txt" "$TMP/env-modules.txt"; then
    ok import-closure "$n_src source files, $n_env modules, the same names"
  else
    LC_ALL=C comm -23 "$TMP/source-modules.txt" "$TMP/env-modules.txt" \
      | sed 's/^/  SOURCE FILE NOT IMPORTED BY VoltageToBit.lean (not built, not audited): /'
    LC_ALL=C comm -13 "$TMP/source-modules.txt" "$TMP/env-modules.txt" \
      | sed 's/^/  MODULE IN THE ENVIRONMENT WITHOUT A SOURCE FILE: /'
    fail import-closure "$n_src source files but $n_env modules in the audited environment, or different names"
  fi
fi

# ---------------------------------------------------------------------------
# versions and the list of what was checked (written by every run)
MATHLIB_REV="$(python3 -c 'import json
for p in json.load(open("lake-manifest.json"))["packages"]:
    if p["name"] == "mathlib":
        print(p["rev"])')"
{
  lean --version
  lake --version
  echo "mathlib rev: $MATHLIB_REV"
} >"$EVIDENCE/versions.txt"
python3 -c 'import hashlib, pathlib
files = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "VoltageToBit.lean"]
files += sorted(p.as_posix() for p in pathlib.Path("VoltageToBit").rglob("*.lean"))
for f in files:
    print(hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest() + "  " + f)' >"$EVIDENCE/sources.sha256"
SOURCES_DIGEST="$(sha256_of "$EVIDENCE/sources.sha256")"
echo "== versions =="
cat "$EVIDENCE/versions.txt"
echo "sources: $(count_lines "$EVIDENCE/sources.sha256") files listed in $EVIDENCE/sources.sha256 (sha256 of the list: $SOURCES_DIGEST)"

if [ "$QUICK" = 1 ]; then
  echo "== 6 to 8. kernel replay: SKIPPED (--quick) =="
  if [ -f "$EVIDENCE/kernel-replay.txt" ]; then
    if grep -q "sha256 of the list: $SOURCES_DIGEST" "$EVIDENCE/kernel-replay.txt"; then
      echo "the record $EVIDENCE/kernel-replay.txt of an earlier full run is for these same sources"
    else
      echo "the record $EVIDENCE/kernel-replay.txt of an earlier full run is for DIFFERENT sources"
    fi
  fi
  last_line
fi

# ---------------------------------------------------------------------------
# kernel replay. Everything below reads compiled files, so it needs the build.
if failed build || [ ! -f "$TMP/lists/constants.txt" ]; then
  echo "== 6 to 8. kernel replay: not run, the build or the audit did not complete =="
  fail replay-modules "not run"
  last_line
fi

TCBIN="$(dirname "$(lake env which lean)")"
RECORD="$TMP/kernel-replay.txt"
N_MODULES="$(count_lines "$TMP/env-modules.txt")"
N_CHECKABLE="$(count_lines "$TMP/lists/constants.txt")"
N_SKIPPED="$(count_lines "$TMP/lists/skipped.txt")"
ENVIRONMENT="$(sed -n 's/^imported environment: //p' "$EVIDENCE/audit.txt")"

tool_id() {   # tool_id <executable name>: how the record names the tool
  if [ -x "$TCBIN/$1" ]; then
    echo "$1, in the bin directory of the toolchain (sha256 of the executable: $(sha256_of "$TCBIN/$1"))"
  else
    echo "$1: NOT FOUND in $TCBIN"
  fi
}

{
  echo "Kernel replay record. Written by scripts/check.sh; do not edit."
  echo "It has no dates or timings: a run on the same sources with the same tools reproduces it."
  echo
  echo "What was checked"
  echo "  sources:   the files listed in $EVIDENCE/sources.sha256 (sha256 of the list: $SOURCES_DIGEST)"
  echo "  toolchain: $(lean --version)"
  echo "  mathlib:   $MATHLIB_REV"
  echo "  library:   $N_MODULES modules; $N_CHECKABLE declarations that a kernel can check, and"
  echo "             $N_SKIPPED compiler auxiliaries that none checks (named in $EVIDENCE/audit.txt)"
  echo "  imported environment, of which the library is a part: $ENVIRONMENT"
} >"$RECORD"

# --- step 6 ---------------------------------------------------------------
echo "== 6. leanchecker: compiled modules replayed against their imports (up to $JOBS at a time) =="
START="$(date +%s)"
{
  echo
  echo "1. Compiled modules replayed against the imported environment"
  echo "  tool:    $(tool_id leanchecker)"
  echo "  command: LEAN_NUM_THREADS=<jobs> lake env leanchecker -v VoltageToBit"
  echo "  does:    for every module whose name starts with VoltageToBit, sends each declaration"
  echo "           stored in the module's compiled file (the compiler auxiliaries excepted) to"
  echo "           Lean's kernel, on top of the environment formed by the module's imports. The"
  echo "           imports themselves (other modules of the library, Mathlib, Lean core) are"
  echo "           loaded as compiled; they are not re-checked by this step."
} >>"$RECORD"
if [ ! -x "$TCBIN/leanchecker" ]; then
  echo "  result:  not run, the tool is missing" >>"$RECORD"
  fail replay-modules "leanchecker not found in $TCBIN"
else
  LEAN_ABORT_ON_PANIC=1 LEAN_NUM_THREADS="$JOBS" lake env "$TCBIN/leanchecker" -v VoltageToBit \
    >"$TMP/leanchecker.log" 2>&1
  status=$?
  grep '^replaying ' "$TMP/leanchecker.log" | sed 's/^replaying //' | LC_ALL=C sort >"$TMP/replayed-modules.txt"
  filter <"$TMP/leanchecker.log" | grep -v '^replaying ' | cut -c1-600 | head -n 40
  n_rep="$(count_lines "$TMP/replayed-modules.txt")"
  {
    echo "  modules replayed ($n_rep):"
    indent <"$TMP/replayed-modules.txt"
    echo "  exit status: $status"
  } >>"$RECORD"
  echo "modules replayed: $n_rep; exit status $status; $(( $(date +%s) - START )) s"
  if [ "$status" != 0 ]; then
    fail replay-modules "leanchecker exited with status $status: the kernel rejects a declaration, see above"
  elif ! cmp -s "$TMP/replayed-modules.txt" "$TMP/env-modules.txt"; then
    LC_ALL=C comm -3 "$TMP/replayed-modules.txt" "$TMP/env-modules.txt"
    fail replay-modules "the modules replayed are not the modules of the audited environment (a compiled file without a source? try --fresh)"
  else
    ok replay-modules "$n_rep modules"
    REPLAYED="the compiled files of $n_rep modules of the library, against their imports, by leanchecker"
  fi
fi

# --- steps 7 and 8 --------------------------------------------------------
# check_export <step prefix> <export file> <hard error on unexpected axiom: true|false>
# Runs the six checkers on an export and appends to the record. Sets ACCEPTED
# to the names of the tools that accepted it.
check_export() {
  ce_step="$1"; ce_file="$2"; ce_hard="$3"
  ACCEPTED=""
  cat >"$TMP/nanoda.json" <<EOF
{
  "export_file_path": "$ce_file",
  "use_stdin": false,
  "permitted_axioms": [$STANDARD_AXIOMS],
  "unpermitted_axiom_hard_error": $ce_hard,
  "nat_extension": true,
  "string_extension": true,
  "num_threads": 4,
  "pp_to_stdout": true,
  "print_success_message": true
}
EOF
  # name | executable | arguments before the file | pattern of the success line | description
  while IFS='|' read -r ce_name ce_exe ce_args ce_pattern ce_what; do
    [ -n "$ce_name" ] || continue
    ce_start="$(date +%s)"
    {
      echo "  $ce_name: $ce_what"
      echo "    tool:        $(tool_id "$ce_exe")"
    } >>"$RECORD"
    if [ ! -x "$TCBIN/$ce_exe" ]; then
      echo "    result:      not run, the tool is missing" >>"$RECORD"
      fail "$ce_step/$ce_name" "$ce_exe not found in $TCBIN"
      continue
    fi
    if [ "$ce_name" = nanoda ]; then
      echo "    command:     nanoda_bin <configuration naming the export; axioms permitted: $STANDARD_AXIOMS;" >>"$RECORD"
      echo "                 an axiom outside that list is a hard error: $ce_hard>" >>"$RECORD"
      ce_version="$("$TCBIN/$ce_exe" --help 2>/dev/null | head -n 1)"
      echo "    version:     $ce_version" >>"$RECORD"
      (cd "$TMP" && LEAN_ABORT_ON_PANIC=1 "$TCBIN/$ce_exe" "$TMP/nanoda.json") </dev/null >"$TMP/checker.log" 2>&1
      ce_status=$?
    else
      echo "    command:     $ce_exe $ce_args <export>" >>"$RECORD"
      # shellcheck disable=SC2086
      (cd "$TMP" && LEAN_ABORT_ON_PANIC=1 "$TCBIN/$ce_exe" $ce_args "$ce_file") </dev/null >"$TMP/checker.log" 2>&1
      ce_status=$?
    fi
    ce_line="$(grep -E "$ce_pattern" "$TMP/checker.log" | tail -n 1)"
    {
      echo "    exit status: $ce_status"
      echo "    it printed:  ${ce_line:-<no line of the expected form>}"
    } >>"$RECORD"
    echo "$ce_name: exit status $ce_status; ${ce_line:-no line of the expected form}; $(( $(date +%s) - ce_start )) s"
    if [ "$ce_status" = 0 ] && [ -n "$ce_line" ]; then
      ok "$ce_step/$ce_name"
      ACCEPTED="$ACCEPTED${ACCEPTED:+, }$ce_name"
    else
      # the reason is at the top for some tools and at the bottom for others
      filter <"$TMP/checker.log" | cut -c1-600 | head -n 4
      echo "    ..."
      filter <"$TMP/checker.log" | cut -c1-600 | tail -n 8
      fail "$ce_step/$ce_name" "exit status $ce_status"
    fi
  done <<'EOF'
leanchecker|leanchecker|--from-export|^Lean default kernel accepts the solution$|Lean's own kernel, the one that also checks declarations when a file is compiled
leanchecker-paranoid|leanchecker-paranoid|--from-export|^Lean default kernel accepts the solution$|the same program in a separate, statically linked build; its output does not say what the build changes, so it is not counted as an independent implementation
lean4lean|lean4lean|--import|^checked [0-9]+ declarations$|a kernel written in Lean by Mario Carneiro: an implementation separate from Lean's own
nanoda|nanoda_bin||^Checked [0-9]+ declarations with no errors|a kernel written in Rust by Chris Bailey: an implementation separate from Lean's own
con-leche|con-leche|--jobs=4|^con-leche: accepted [0-9]+ declarations \(--verified\)$|a checker by the Lean FRO written in Lean; described here only from its --help, which presents it as a checker of its own with a proved soundness statement
con-ron|con-ron|--jobs=4|^con-ron: accepted [0-9]+ declarations \(--verified\)$|a checker by the Lean FRO written in Rust; described here only from its --help, which presents it as a Rust version of con-leche
EOF
}

export_library() {   # the names are passed as arguments, one per declaration
  set --
  while IFS= read -r name; do set -- "$@" "$name"; done <"$TMP/lists/constants.txt"
  LEAN_ABORT_ON_PANIC=1 lake env "$TCBIN/leanexport" VoltageToBit -- "$@" >"$TMP/library.ndjson" 2>"$TMP/export.log"
}

echo "== 7. leanexport: the library's declarations and everything they depend on =="
START="$(date +%s)"
{
  echo
  echo "2. Export of the declarations of the library with everything they depend on"
  echo "  tool:    $(tool_id leanexport)"
  echo "  command: lake env leanexport VoltageToBit -- <the $N_CHECKABLE declaration names>"
  echo "  does:    writes the named declarations, and every declaration that occurs in the type or"
  echo "           in the value of one already written, to one file. So the file contains the part"
  echo "           of Mathlib, of its dependencies and of Lean core that the library depends on,"
  echo "           proofs included, and nothing of the rest of the imported environment."
} >>"$RECORD"
EXPORT_OK=0
if [ ! -x "$TCBIN/leanexport" ]; then
  echo "  result:  not run, the tool is missing" >>"$RECORD"
  fail export "leanexport not found in $TCBIN"
else
  export_library
  status=$?
  filter <"$TMP/export.log" | cut -c1-600 | head -n 20
  python3 scripts/export_census.py "$TMP/library.ndjson" --require "$TMP/lists/constants.jsonl" >"$TMP/census.txt" 2>&1
  census_status=$?
  cat "$TMP/census.txt"
  {
    echo "  exit status: $status"
    echo "  contents, as read by scripts/export_census.py (exit status $census_status):"
    indent <"$TMP/census.txt"
  } >>"$RECORD"
  echo "$(( $(date +%s) - START )) s"
  if [ "$status" = 0 ] && [ "$census_status" = 0 ]; then
    ok export "$(grep '^declarations of the library present' "$TMP/census.txt")"
    EXPORT_OK=1
  else
    fail export "leanexport exited with status $status, the census with status $census_status"
  fi
fi

echo "== 8. the export re-checked from an empty environment =="
{
  echo
  echo "3. The export re-checked from an empty environment"
  echo "  Each tool reads the export file and nothing else: no compiled file of the library, of"
  echo "  Mathlib or of Lean core. Every declaration in the file is checked again, in the order"
  echo "  of its dependencies."
} >>"$RECORD"
if [ "$EXPORT_OK" = 1 ]; then
  check_export replay-export "$TMP/library.ndjson" true
  N_OUTSIDE="$(sed -n 's/^declarations from outside the library[^:]*: //p' "$TMP/census.txt")"
  if [ -n "$ACCEPTED" ]; then
    REPLAYED="$REPLAYED; the $N_CHECKABLE declarations of the library and the $N_OUTSIDE declarations of Mathlib, its dependencies and Lean core that they depend on, from an empty environment, by $ACCEPTED"
  fi
else
  echo "  not run: there is no export" >>"$RECORD"
  echo "not run: there is no export"
  fail replay-export "not run: there is no export"
fi
rm -f "$TMP/library.ndjson"

# --- step 9 ---------------------------------------------------------------
{
  echo
  echo "4. The whole imported environment (optional, scripts/check.sh --whole-env)"
} >>"$RECORD"
if [ "$WHOLE" = 0 ]; then
  {
    echo "  not run. Declarations of Mathlib and of Lean core that the library does not depend on"
    echo "  were not re-checked."
  } >>"$RECORD"
  REPLAYED="$REPLAYED. Not re-checked: the declarations of the imported environment ($ENVIRONMENT) that the library does not depend on (--whole-env does that)."
else
  echo "== 9. leanchecker --fresh: the whole imported environment, from an empty environment =="
  START="$(date +%s)"
  {
    echo "  tool:    $(tool_id leanchecker)"
    echo "  command: lake env leanchecker --fresh VoltageToBit"
    echo "  does:    loads the compiled files of VoltageToBit and of every module it imports, directly"
    echo "           or not ($ENVIRONMENT),"
    echo "           and sends every declaration in them to Lean's kernel, starting from an empty"
    echo "           environment. The tool leaves out the definitions marked unsafe or partial, which"
    echo "           exist for the compiler ($EVIDENCE/audit.txt has their number). Unlike 1 this"
    echo "           re-checks Mathlib and Lean core themselves, whether the library uses a"
    echo "           declaration or not. It is Lean's own kernel: no independent implementation was"
    echo "           run on the whole environment."
  } >>"$RECORD"
  if [ ! -x "$TCBIN/leanchecker" ]; then
    echo "  result:  not run, the tool is missing" >>"$RECORD"
    fail whole-env "leanchecker not found in $TCBIN"
  else
    LEAN_ABORT_ON_PANIC=1 lake env "$TCBIN/leanchecker" --fresh VoltageToBit >"$TMP/fresh.log" 2>&1
    status=$?
    filter <"$TMP/fresh.log" | cut -c1-600 | head -n 20
    echo "  exit status: $status" >>"$RECORD"
    echo "exit status $status; $(( $(date +%s) - START )) s"
    if [ "$status" = 0 ]; then
      ok whole-env "$ENVIRONMENT"
      REPLAYED="$REPLAYED; every declaration of the imported environment ($ENVIRONMENT; those marked unsafe or partial are compiler-only and are left out), Mathlib included, from an empty environment, by leanchecker --fresh (Lean's own kernel only)."
    else
      fail whole-env "leanchecker --fresh exited with status $status"
    fi
  fi
fi

last_line
