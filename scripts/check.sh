#!/bin/sh
# Reproduce every formal check of this repository.
#
#   scripts/check.sh               steps 1 to 8
#   scripts/check.sh --quick       steps 1 to 5: nothing is re-checked by a kernel
#   scripts/check.sh --whole-env   steps 1 to 9
#   --fresh        delete this project's own build products first, so that
#                  every file of this project is recompiled (.lake/packages,
#                  the prebuilt Mathlib, is kept)
#   --keep-going   do not stop at the first failing step: run every step whose
#                  inputs exist and report each one
#
# Steps. Each prints "RESULT <step>: ok" or "RESULT <step>: FAILED"; a tool
# that is not installed prints "RESULT <step>: NOT RUN" (see Tools).
#   1 design-record   every generated Lean design record is what its JSON file
#                     generates, and every JSON file in designs/ has one
#   2 source-scan     the library sources and lakefile.toml contain no
#                     construct that can bypass the kernel or change how later
#                     text is elaborated (scripts/lean_scan.py: a deny-list
#                     and allow-lists over the text; a tripwire, not a proof)
#   3 build           `lake build` exits with status 0
#   4 axiom-audit     no declaration of the library depends on an axiom beyond
#                     propext, Classical.choice, Quot.sound; the library
#                     declares no axiom, opaque or unsafe constant, instance
#                     or simp lemma of its own (scripts/Audit.lean, which
#                     looks at every declaration, not at a list of names)
#   5 import-closure  the .lean files of the library are exactly the modules
#                     of the library in the audited environment
#   6 replay-modules  `leanchecker` sends the declarations stored in the
#                     compiled file of every module of the library to Lean's
#                     kernel again, on top of that module's imports as they
#                     are compiled (Mathlib is loaded, not re-checked)
#   7 export          `leanexport` writes every declaration of the library,
#                     and every declaration those depend on, directly or not
#                     (the part of Mathlib, of its dependencies and of Lean
#                     core that the library uses, proofs included), to one
#                     file; scripts/export_census.py confirms that every
#                     declaration of the library is in it
#   8 replay-export   that file is checked from an empty environment by each
#                     of the six checkers listed under Tools
#   9 whole-env       (--whole-env only) `leanchecker --fresh` sends every
#                     declaration of every module that the library imports,
#                     directly or not, to Lean's kernel, from an empty
#                     environment, whether the library uses the declaration
#                     or not. That is the part of Mathlib that the library
#                     imports, its dependencies and Lean core; modules of
#                     Mathlib that the library does not import are not
#                     compiled here and are never looked at
#
# Tools. Every executable is taken from the bin directory of the toolchain
# that lean-toolchain pins (the directory of `lake env which lean`) and from
# nowhere else. `lake help check` of that toolchain names the checkers it
# bundles; the record quotes the sentence. A tool that is not in that
# directory (another toolchain version, a toolchain built from source) is
# reported as NOT RUN, by name, in the output, in the record and in the last
# line, and is not counted; the last line then begins differently (see Exit
# status). Only leanchecker is required: without it steps 6 and 9 fail.
#   leanchecker           Lean's own kernel (steps 6, 8 and 9). Its source is
#                         in the toolchain: src/lean/LeanChecker.lean.
#   leanchecker-paranoid  Lean's own kernel again, in an executable of its
#                         own with the same options and messages; not counted
#                         as an independent implementation (step 8).
#   lean4lean, nanoda_bin, con-leche, con-ron
#                         four programs that are not Lean's kernel, according
#                         to `lake help check`, to the toolchain's LICENSES
#                         file and, where a tool has one, to its --help
#                         (step 8). Their sources are not in the toolchain
#                         and were not read; the record says of each what is
#                         known and where from. Where a tool reports how many
#                         declarations it checked, the number must be the one
#                         that scripts/export_census.py finds in the export.
#   leanexport            writes the export (step 7); it checks nothing.
# These descriptions were written for the toolchain named in DESCRIBED_FOR
# below; with another one the script says so and they have to be re-read.
#
# What a pass establishes. The last line of output says which parts apply.
#   steps 1 to 5 (all that --quick does): the library compiles; no declaration
#     in the compiled files depends on an axiom beyond the three of step 4;
#     every .lean file of the library is part of what was compiled and
#     audited; the design records match their JSON files. Nothing has been
#     re-checked: a declaration that was added with the kernel check switched
#     off passes steps 3 and 4 (scripts/selftest.sh demonstrates it), and
#     step 2 is only a scan of the text.
#   step 6: every declaration in the compiled files of the library (the
#     compiler auxiliaries named in the audit excepted) is accepted by Lean's
#     kernel on top of the compiled Mathlib.
#   steps 7 and 8: the declarations of the library, together with every
#     declaration of Mathlib, its dependencies and Lean core that they depend
#     on, are accepted from an empty environment by each checker that the last
#     line names.
#   step 9: every declaration of every module that the library imports is
#     accepted by Lean's kernel from an empty environment.
# What it does not establish: that the statements mean what the prose says
# (read them), or that any physical device obeys the model. Nor
#   - that the export is faithful: the checkers of step 8 read what
#     `leanexport` wrote, not the compiled files (step 6 reads those, for the
#     library's own declarations);
#   - anything about how Lean turned the source text into those declarations;
#   - anything about declarations of Mathlib that the library does not depend
#     on, unless --whole-env is given (then those in imported modules are
#     re-checked, by Lean's own kernel only);
#   - that the four other checkers are sound, or independent of each other:
#     they are run as shipped.
#
# Records are written to evidence/lean/: audit.txt, source-scan.txt,
# versions.txt and sources.sha256 by every run, kernel-replay.txt by every run
# without --quick. They contain no dates or timings, so a run with the same
# options on the same files with the same tools reproduces them byte for byte.
#
# Each step prints the seconds it took. Step 6 takes time in proportion to the
# number of modules, steps 7 and 8 to the size of what the library depends on,
# step 9 to the size of the whole imported environment.
#
# Environment: CHECK_REPLAY_JOBS (default 1) is the number of modules that
# `leanchecker` replays at a time in step 6. Every job beyond the first was
# measured to need several GB of memory of its own, and on a machine short of
# memory two jobs were no faster than one.
#
# Exit status: 0 every step that was run passed; 1 a step failed; 2 usage.
# The last line of output says which happened. On success it begins with
# "ALL FORMAL CHECKS PASSED." if every tool was installed, with "THE FORMAL
# CHECKS THAT WERE RUN PASSED; NOT EVERY TOOL IS INSTALLED." otherwise, with
# "QUICK CHECK PASSED" for --quick, and goes on to say exactly what was
# replayed and by which tools, or that nothing was.
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
JOBS="${CHECK_REPLAY_JOBS:-1}"
case "$JOBS" in
  ''|0*|*[!0-9]*)
    echo "check.sh: CHECK_REPLAY_JOBS must be a whole number, 1 or more; got '$JOBS'" >&2; exit 2 ;;
esac

DESCRIBED_FOR="leanprover/lean4:v4.35.0"   # the toolchain whose tools are described here
EVIDENCE=evidence/lean
STANDARD_AXIOMS='"propext", "Classical.choice", "Quot.sound"'

TMP="$(mktemp -d "${TMPDIR:-/tmp}/vtb-check.XXXXXX")" || exit 2
trap 'rm -rf "$TMP"' EXIT
trap 'exit 130' INT TERM
mkdir -p "$TMP/lists" "$TMP/empty" "$EVIDENCE"

T0="$(date +%s)"
FAILED=""            # steps that failed
NOTRUN=""            # tools that are not installed, by name
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
since() { echo "$(( $(date +%s) - $1 )) s"; }

last_line() {
  if [ -f "$TMP/kernel-replay.txt" ]; then
    {
      echo
      echo "Summary"
      echo "  tools not run because they are not installed: ${NOTRUN:-none}"
      if [ -n "$FAILED" ]; then
        echo "  outcome of the run of scripts/check.sh that wrote this record: FAILED:$FAILED"
      else
        echo "  outcome of the run of scripts/check.sh that wrote this record: every step that was run passed."
        echo "  kernel replay: $REPLAYED"
      fi
    } >>"$TMP/kernel-replay.txt"
    cp "$TMP/kernel-replay.txt" "$EVIDENCE/kernel-replay.txt"
    echo "record written to $EVIDENCE/kernel-replay.txt"
  fi
  echo "elapsed: $(since "$T0")"
  if [ -n "$FAILED" ]; then
    echo "CHECK FAILED:$FAILED"
    exit 1
  fi
  if [ "$QUICK" = 1 ]; then
    echo "QUICK CHECK PASSED (steps 1 to 5). THE KERNEL REPLAY WAS SKIPPED (--quick): no declaration was re-checked by any kernel in this run."
  elif [ -z "$NOTRUN" ]; then
    echo "ALL FORMAL CHECKS PASSED. Kernel replay: $REPLAYED"
  else
    echo "THE FORMAL CHECKS THAT WERE RUN PASSED; NOT EVERY TOOL IS INSTALLED. Kernel replay: $REPLAYED"
  fi
  exit 0
}
ok() { echo "RESULT $1: ok${2:+ ($2)}"; }
fail() {
  echo "RESULT $1: FAILED ($2)"
  FAILED="$FAILED $1"
  if [ "$KEEP" = 0 ]; then last_line; fi
}
# notrun <step> <tool>: the tool is not installed; it is named and not counted
notrun() {
  echo "RESULT $1: NOT RUN ($2 is not in the bin directory of the toolchain, $TCBIN; it is not counted)"
  NOTRUN="$NOTRUN${NOTRUN:+, }$2"
}
# failed <step>: has this step, or a step whose name starts with it, failed?
failed() { case " $FAILED " in *" $1"*) return 0 ;; *) return 1 ;; esac; }

if [ "$FRESH" = 1 ]; then
  echo "== 0. removing this project's build products =="
  rm -rf .lake/build
fi

# ---------------------------------------------------------------------------
echo "== 1. design records in sync with their JSON files =="
if python3 scripts/gen_design.py --check-all designs VoltageToBit; then
  ok design-record
else
  fail design-record "a generated design record is stale, a JSON design file was rejected or has no generated record; see the message above"
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
START="$(date +%s)"
lake build >"$TMP/build.log" 2>&1
status=$?
if [ "$status" = 0 ]; then
  filter <"$TMP/build.log" | tail -n 3
  echo "$(since "$START")"
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
  START="$(date +%s)"
  VTB_AUDIT_LISTS="$TMP/lists" lake env lean scripts/Audit.lean >"$TMP/audit.log" 2>&1
  status=$?
  filter <"$TMP/audit.log" >"$EVIDENCE/audit.txt"
  sed '/^theorems with a name of their own/,$d' "$EVIDENCE/audit.txt" | cut -c1-2000
  echo "$(since "$START")"
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
files += sorted(p.as_posix() for p in pathlib.Path("designs").glob("*.json"))
files += sorted(p.as_posix() for p in pathlib.Path("scripts").iterdir()
                if p.is_file() and p.suffix in (".sh", ".py", ".lean"))
for f in files:
    print(hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest() + "  " + f)' >"$EVIDENCE/sources.sha256"
SOURCES_DIGEST="$(sha256_of "$EVIDENCE/sources.sha256")"
echo "== versions =="
cat "$EVIDENCE/versions.txt"
echo "files: $(count_lines "$EVIDENCE/sources.sha256") (library sources, build configuration, design files, checking scripts) listed in $EVIDENCE/sources.sha256 (sha256 of the list: $SOURCES_DIGEST)"
TOOLCHAIN_NOTE=""
if [ "$(cat lean-toolchain)" != "$DESCRIBED_FOR" ]; then
  TOOLCHAIN_NOTE="NOTE: lean-toolchain says $(cat lean-toolchain), but the descriptions of the tools in scripts/check.sh were written for $DESCRIBED_FOR; re-read them (--help of each tool) before relying on them."
  echo "$TOOLCHAIN_NOTE"
fi

if [ "$QUICK" = 1 ]; then
  echo "== 6 to 8. kernel replay: SKIPPED (--quick) =="
  if [ -f "$EVIDENCE/kernel-replay.txt" ]; then
    if grep -q "sha256 of the list: $SOURCES_DIGEST" "$EVIDENCE/kernel-replay.txt"; then
      echo "the record $EVIDENCE/kernel-replay.txt of an earlier full run is for these same files"
    else
      echo "the record $EVIDENCE/kernel-replay.txt of an earlier full run is for DIFFERENT files"
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
BUNDLED="$(lake help check 2>/dev/null \
  | awk '/^  --paranoid/{p=1; print; next} p && /^  --/{p=0} p && NF{print}' \
  | sed 's/^ *//' | tr '\n' ' ' | sed 's/  */ /g; s/ $//')"

tool_id() {   # tool_id <executable name>: how the record identifies the executable
  if [ -x "$TCBIN/$1" ]; then
    echo "$1, in the bin directory of the toolchain (sha256 of the executable: $(sha256_of "$TCBIN/$1"))"
  else
    echo "$1: not in the bin directory of the toolchain"
  fi
}

{
  echo "Kernel replay record. Written by scripts/check.sh; do not edit."
  echo "It has no dates or timings: a run with the same options on the same files with the same"
  echo "tools reproduces it."
  echo
  echo "What was checked"
  echo "  files:     the library sources, build configuration, design files and checking scripts"
  echo "             listed in $EVIDENCE/sources.sha256 (sha256 of the list: $SOURCES_DIGEST)"
  echo "  toolchain: $(lean --version)"
  echo "  mathlib:   $MATHLIB_REV"
  echo "  library:   $N_MODULES modules; $N_CHECKABLE declarations that the replay steps re-check, and"
  echo "             $N_SKIPPED compiler auxiliaries that they leave out (named in $EVIDENCE/audit.txt)"
  echo "  imported environment, of which the library is a part: $ENVIRONMENT"
  echo
  echo "Where the tools come from"
  echo "  Every executable named below was looked for in the bin directory of the toolchain that"
  echo "  lean-toolchain pins (the directory of \`lake env which lean\`) and nowhere else. A tool that"
  echo "  is not there is reported as NOT RUN and is not counted."
  if [ -n "$BUNDLED" ]; then
    echo "  \`lake help check\` of this toolchain says about the checkers it bundles:"
    echo "    $BUNDLED"
  else
    echo "  \`lake help check\` of this toolchain does not name any bundled checker."
  fi
  if [ -n "$TOOLCHAIN_NOTE" ]; then echo "  $TOOLCHAIN_NOTE"; fi
} >"$RECORD"

# --- step 6 ---------------------------------------------------------------
echo "== 6. leanchecker: compiled modules replayed against their imports ($JOBS at a time) =="
START="$(date +%s)"
{
  echo
  echo "1. Compiled modules replayed against the imported environment"
  echo "  tool:    $(tool_id leanchecker)"
  echo "  kind:    Lean's own kernel, the one that also checks declarations when a file is compiled"
  echo "  command: LEAN_NUM_THREADS=<jobs> lake env leanchecker -v VoltageToBit"
  echo "  does:    for every module whose name starts with VoltageToBit, sends each declaration"
  echo "           stored in the module's compiled file (the compiler auxiliaries excepted) to"
  echo "           Lean's kernel, on top of the environment formed by the module's imports. The"
  echo "           imports themselves (other modules of the library, Mathlib, Lean core) are"
  echo "           loaded as compiled; they are not re-checked by this step."
} >>"$RECORD"
if [ ! -x "$TCBIN/leanchecker" ]; then
  echo "  result:  not run, the tool is missing" >>"$RECORD"
  fail replay-modules "leanchecker is not in $TCBIN, and this step needs it (--quick skips the replay)"
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
  echo "modules replayed: $n_rep; exit status $status; $(since "$START")"
  if [ "$status" != 0 ]; then
    echo "  RESULT replay-modules: FAILED" >>"$RECORD"
    fail replay-modules "leanchecker exited with status $status; its message is above (a declaration that the kernel rejects is named there)"
  elif ! cmp -s "$TMP/replayed-modules.txt" "$TMP/env-modules.txt"; then
    LC_ALL=C comm -3 "$TMP/replayed-modules.txt" "$TMP/env-modules.txt"
    echo "  RESULT replay-modules: FAILED" >>"$RECORD"
    fail replay-modules "the modules replayed are not the modules of the audited environment (a compiled file without a source? try --fresh)"
  else
    echo "  RESULT replay-modules: ok" >>"$RECORD"
    ok replay-modules "$n_rep modules"
    REPLAYED="(1) the compiled files of the $n_rep modules of the library, each on top of its imports as compiled, by leanchecker (Lean's own kernel)."
  fi
fi

# --- steps 7 and 8 --------------------------------------------------------
# check_export <step prefix> <export file> <hard error on unexpected axiom: true|false>
# Runs the checkers on an export and appends to the record. Sets
# ACCEPTED_KERNEL and ACCEPTED_SEPARATE to the names of the tools that accepted it.
# Each tool is started in an empty directory with an empty environment, and is
# given the export (for nanoda: a configuration naming it) and nothing else.
# Needs N_RECORDS, N_RECORDS_QUOT and N_CONSTANTS, the contents of the export
# as counted by scripts/export_census.py.
check_export() {
  ce_step="$1"; ce_file="$2"; ce_hard="$3"
  ACCEPTED_KERNEL=""; ACCEPTED_SEPARATE=""
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
  # name | executable | kind | what the number in its success line counts | arguments before
  # the file | pattern of the success line | what is known of it
  while IFS='|' read -r ce_name ce_exe ce_kind ce_count ce_args ce_pattern ce_what; do
    [ -n "$ce_name" ] || continue
    ce_start="$(date +%s)"
    case "$ce_count" in
      records)
        ce_expected="$N_RECORDS"
        ce_counted="one per declaration record of the export, which is what its --help says it counts" ;;
      records-quot)
        ce_expected="$N_RECORDS_QUOT"
        ce_counted="one per declaration record of the export with the quotient records as one; seen on small exports, not documented" ;;
      constants)
        ce_expected="$N_CONSTANTS"
        ce_counted="one per constant that the export declares; seen on small exports, not documented" ;;
      *)
        ce_expected=""; ce_counted="" ;;
    esac
    if [ "$ce_kind" = kernel ]; then
      ce_kind_text="Lean's own kernel"
    else
      ce_kind_text="a separate program, not Lean's kernel, as far as the following says"
    fi
    {
      echo "  $ce_name"
      echo "    kind:        $ce_kind_text"
      echo "    known of it: $ce_what"
      echo "    tool:        $(tool_id "$ce_exe")"
    } >>"$RECORD"
    echo "-- $ce_name --"
    if [ ! -x "$TCBIN/$ce_exe" ]; then
      echo "    RESULT $ce_step/$ce_name: NOT RUN" >>"$RECORD"
      notrun "$ce_step/$ce_name" "$ce_exe"
      continue
    fi
    if [ "$ce_name" = nanoda ]; then
      ce_version="$(cd "$TMP/empty" && env -i "$TCBIN/$ce_exe" --help 2>/dev/null </dev/null | head -n 1)"
      {
        echo "    it calls itself: $ce_version"
        echo "    command:     nanoda_bin <configuration naming the export; axioms permitted: $STANDARD_AXIOMS;"
        echo "                 an axiom outside that list is a hard error: $ce_hard>"
      } >>"$RECORD"
      set -- "$TMP/nanoda.json"
    else
      echo "    command:     $ce_exe $ce_args <export>" >>"$RECORD"
      # shellcheck disable=SC2086
      set -- $ce_args "$ce_file"
    fi
    # "; exit $?" keeps the shell's own report of a tool killed by a signal in the tool's log
    (cd "$TMP/empty" && env -i LEAN_ABORT_ON_PANIC=1 "$TCBIN/$ce_exe" "$@"; exit $?) </dev/null >"$TMP/checker.log" 2>&1
    ce_status=$?
    ce_line="$(grep -E "$ce_pattern" "$TMP/checker.log" | tail -n 1)"
    ce_reported="$(printf '%s\n' "$ce_line" | sed -n 's/^[^0-9]*\([0-9][0-9]*\).*/\1/p')"
    {
      echo "    exit status: $ce_status"
      echo "    it printed:  ${ce_line:-<no line of the expected form>}"
      if [ -n "$ce_expected" ]; then
        echo "    the export has: $ce_expected, counted its way ($ce_counted)"
      fi
    } >>"$RECORD"
    echo "$ce_name: exit status $ce_status; ${ce_line:-no line of the expected form}; $(since "$ce_start")"
    if [ "$ce_status" = 0 ] && [ -n "$ce_line" ] && [ -n "$ce_expected" ] && [ "$ce_reported" != "$ce_expected" ]; then
      echo "    RESULT $ce_step/$ce_name: FAILED" >>"$RECORD"
      fail "$ce_step/$ce_name" "it reports ${ce_reported:-no number of} declarations, but the export has $ce_expected ($ce_counted)"
    elif [ "$ce_status" = 0 ] && [ -n "$ce_line" ]; then
      echo "    RESULT $ce_step/$ce_name: ok" >>"$RECORD"
      ok "$ce_step/$ce_name"
      if [ "$ce_kind" = kernel ]; then
        ACCEPTED_KERNEL="$ACCEPTED_KERNEL${ACCEPTED_KERNEL:+, }$ce_name"
      else
        ACCEPTED_SEPARATE="$ACCEPTED_SEPARATE${ACCEPTED_SEPARATE:+, }$ce_name"
      fi
    else
      # the reason is at the top for some tools and at the bottom for others
      filter <"$TMP/checker.log" | cut -c1-600 | head -n 4
      echo "    ..."
      filter <"$TMP/checker.log" | cut -c1-600 | tail -n 8
      if grep -q '^PANIC at ' "$TMP/checker.log"; then
        # A Lean program that panics is stopped at once by LEAN_ABORT_ON_PANIC=1, before it can
        # say what it objects to. The verdict above stands; this only shows the message.
        echo "    the same command without LEAN_ABORT_ON_PANIC=1, for its message only (the result is not used):"
        (cd "$TMP/empty" && env -i "$TCBIN/$ce_exe" "$@") </dev/null 2>&1 | filter | cut -c1-600 | tail -n 6
      fi
      echo "    RESULT $ce_step/$ce_name: FAILED" >>"$RECORD"
      fail "$ce_step/$ce_name" "exit status $ce_status"
    fi
  done <<'EOF'
leanchecker|leanchecker|kernel|none|--from-export|^Lean default kernel accepts the solution$|its source is in the toolchain (src/lean/LeanChecker.lean): it reads the export and sends every declaration in it to Lean's kernel, starting from an empty environment
leanchecker-paranoid|leanchecker-paranoid|kernel|none|--from-export|^Lean default kernel accepts the solution$|an executable of its own with the same options and messages as leanchecker (on arm64 macOS it is linked statically, where leanchecker uses the toolchain's shared libraries); the toolchain does not say what else its build changes, so it is not counted as an independent implementation
lean4lean|lean4lean|separate|records-quot|--import|^checked [0-9]+ declarations$|the toolchain's LICENSES file attributes lean4lean to Mario Carneiro; the executable contains code named Lean4Lean.TypeChecker; its source is not in the toolchain and was not read
nanoda|nanoda_bin|separate|constants||^Checked [0-9]+ declarations with no errors|its --help calls it an external type checker for Lean 4 (nanoda_lib); the toolchain's LICENSES file attributes nanoda to Chris Bailey; its source is not in the toolchain and was not read
con-leche|con-leche|separate|records|--jobs=4|^con-leche: accepted [0-9]+ declarations \(--verified\)$|the toolchain's LICENSES file attributes con-leche to the Lean FRO; its --help says that in this mode (--verified, the default) a file that declares a theorem of type False is never accepted, by a theorem about the program (ConLeche.no_False_declaration); neither its source nor that theorem was examined
con-ron|con-ron|separate|records|--jobs=4|^con-ron: accepted [0-9]+ declarations \(--verified\)$|the toolchain's LICENSES file attributes con-ron to the Lean FRO; its --help describes it as con-leche's checker written in Rust; its source was not examined
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
  echo "           proofs included, and nothing of the rest of the imported environment. It checks"
  echo "           nothing; that it writes what is in the compiled files is trusted."
} >>"$RECORD"
EXPORT=missing       # missing: no exporter; failed; ok
if [ ! -x "$TCBIN/leanexport" ]; then
  echo "  RESULT export: NOT RUN" >>"$RECORD"
  notrun export leanexport
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
  echo "$(since "$START")"
  if [ "$status" = 0 ] && [ "$census_status" = 0 ]; then
    echo "  RESULT export: ok" >>"$RECORD"
    ok export "$(grep '^declarations of the library present' "$TMP/census.txt")"
    EXPORT=ok
  else
    echo "  RESULT export: FAILED" >>"$RECORD"
    EXPORT=failed
    fail export "leanexport exited with status $status, the census with status $census_status"
  fi
fi

echo "== 8. the export re-checked from an empty environment =="
{
  echo
  echo "3. The export re-checked from an empty environment"
  echo "  Each tool is started in an empty directory with an empty environment (LEAN_ABORT_ON_PANIC=1"
  echo "  apart) and is given the export file and nothing else. A tool passes if it exits with status"
  echo "  0 and prints its line of acceptance; where that line says how many declarations were"
  echo "  checked, the number must be the one that scripts/export_census.py finds in the export."
} >>"$RECORD"
if [ "$EXPORT" = ok ]; then
  N_RECORDS="$(sed -n 's/^declaration records: \([0-9][0-9]*\) .*/\1/p' "$TMP/census.txt")"
  N_RECORDS_QUOT="$(sed -n 's/^declaration records, the quotient records counted as one: //p' "$TMP/census.txt")"
  N_CONSTANTS="$(sed -n 's/^constants declared[^:]*: //p' "$TMP/census.txt")"
  check_export replay-export "$TMP/library.ndjson" true
  N_OUTSIDE="$(sed -n 's/^declarations from outside the library[^:]*: //p' "$TMP/census.txt")"
  if [ -n "$ACCEPTED_KERNEL$ACCEPTED_SEPARATE" ]; then
    REPLAYED="$REPLAYED (2) an export of the $N_CHECKABLE declarations of the library with the $N_OUTSIDE declarations of Mathlib, its dependencies and Lean core that they depend on, from an empty environment, by ${ACCEPTED_KERNEL:-no tool} (Lean's own kernel) and by ${ACCEPTED_SEPARATE:-no tool} (programs that are not Lean's kernel, run as the toolchain ships them)."
  else
    REPLAYED="$REPLAYED (2) NO checker was run on the export."
  fi
elif [ "$EXPORT" = missing ]; then
  echo "  RESULT replay-export: NOT RUN (there is no export)" >>"$RECORD"
  echo "RESULT replay-export: NOT RUN (there is no export, because leanexport is not installed)"
  REPLAYED="$REPLAYED (2) NO export was written and no checker was run on one."
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
  REPLAYED="$REPLAYED Not re-checked: the declarations of the imported modules ($ENVIRONMENT) that the library does not depend on (--whole-env does that)."
else
  echo "== 9. leanchecker --fresh: the whole imported environment, from an empty environment =="
  START="$(date +%s)"
  {
    echo "  tool:    $(tool_id leanchecker)"
    echo "  kind:    Lean's own kernel"
    echo "  command: lake env leanchecker --fresh VoltageToBit"
    echo "  does:    loads the compiled files of VoltageToBit and of every module it imports, directly"
    echo "           or not ($ENVIRONMENT),"
    echo "           and sends every declaration in them to Lean's kernel, starting from an empty"
    echo "           environment. The tool leaves out the definitions marked unsafe or partial, which"
    echo "           exist for the compiler ($EVIDENCE/audit.txt has their number). Unlike 1 this"
    echo "           re-checks the imported modules of Mathlib and Lean core themselves, whether the"
    echo "           library uses a declaration or not. No other checker was run on the whole"
    echo "           environment, and modules of Mathlib that the library does not import are not"
    echo "           part of it."
  } >>"$RECORD"
  if [ ! -x "$TCBIN/leanchecker" ]; then
    echo "  result:  not run, the tool is missing" >>"$RECORD"
    fail whole-env "leanchecker is not in $TCBIN"
  else
    LEAN_ABORT_ON_PANIC=1 lake env "$TCBIN/leanchecker" --fresh VoltageToBit >"$TMP/fresh.log" 2>&1
    status=$?
    filter <"$TMP/fresh.log" | cut -c1-600 | head -n 20
    echo "  exit status: $status" >>"$RECORD"
    echo "exit status $status; $(since "$START")"
    if [ "$status" = 0 ]; then
      echo "  RESULT whole-env: ok" >>"$RECORD"
      ok whole-env "$ENVIRONMENT"
      REPLAYED="$REPLAYED (3) every declaration of every module that the library imports, directly or not ($ENVIRONMENT; those marked unsafe or partial are compiler-only and are left out), the imported part of Mathlib included, from an empty environment, by leanchecker --fresh (Lean's own kernel only)."
    else
      echo "  RESULT whole-env: FAILED" >>"$RECORD"
      fail whole-env "leanchecker --fresh exited with status $status"
    fi
  fi
fi
if [ -n "$NOTRUN" ]; then
  REPLAYED="$REPLAYED NOT RUN, because the executable is not in the toolchain's bin directory: $NOTRUN."
fi

last_line
