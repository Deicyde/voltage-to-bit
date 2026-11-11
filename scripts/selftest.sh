#!/bin/sh
# Negative controls for scripts/check.sh: does it notice what it is there to
# notice, at the step that is meant to notice it?
#
#   scripts/selftest.sh
#
# Nothing in this checkout is modified. Every control works on a throwaway
# copy of the project in a temporary directory (sources, scripts, design
# files; the prebuilt dependencies in .lake/packages are linked, never copied
# or written to). The copy is given a defect and its own scripts/check.sh is
# run on it. A control that adds a module imports only modules that are
# compiled already, so that nothing of Mathlib is built.
#
# One line is printed per control: PASS if check.sh reported the defect at the
# step that is meant to catch it, with the message that names it, FAIL
# otherwise. Exit status 1 if any line is FAIL. The build of this checkout
# must be up to date and evidence/lean/ must hold the records of a full run on
# these files (run scripts/check.sh first). The output has no dates or
# timings. check.sh is run in full twice (on the unmodified copy and on the
# copy with a kernel bypass) and with --quick for the rest; expect the whole
# to take about five times as long as one full run of check.sh. The last line
# says how many PASS lines there are of each kind: negative controls (a defect
# that check.sh must report, or an attack that must change nothing), positive
# controls (an unmodified input that must pass, so that the refusals mean
# something), observations (what the export checkers start from) and the check
# of this checkout.
#
# First, a positive control: a copy without any build product must pass a full
# run, so that a failure below is due to the defect and not to the copying;
# and the records check.sh writes for that copy must be the ones in
# evidence/lean/ of this checkout, which shows that those records can be
# reproduced from the files alone, in another directory. That copy also has a
# hashlib.py and a json.py in its top directory, which end any Python program
# that imports them (py; verification round 4, issue 2): the run must pass, and its
# records be those of the checkout, all the same.
#
# Then the controls, with the finding of the review each one answers ("round 4,
# issue N" is issue N of entry `tooling` of verification round 4):
#   (cfg) the build configuration is not the pinned one: each of a list of
#       changes to lakefile.toml, lake-manifest.json and lean-toolchain, and a
#       lakefile.lean next to lakefile.toml, stops check.sh at step config,
#       before any Lean tool runs (B1, S5); so does each of a list of keys or
#       options of lakefile.toml that could move the library's sources or build
#       products or reach the compiler, srcDir among them, also when the pin is
#       changed to accept the file (round 4, issue 3; options: round 5)
#   (env) in the same group as (cfg), the environment check: called with
#       exactly the environment that check.sh gives itself, it runs; with one
#       variable more, or without
#       PYTHONSAFEPATH, or with a python3 that fails the version test, it stops
#       with exit status 2 before step 1; variables of the caller such as
#       LEAN_PATH and PYTHONPATH (with a json.py in it) change nothing
#       (round 4, issues 2 and 9)
#   (b1) sources that do not compile cannot pass on compiled files left by an
#       earlier build, also when lakefile.toml names no default target or
#       another one and the pin is changed to accept that (B1)
#   (s5) with the autoImplicit lines deleted and the pin changed to accept
#       that, a statement with a misspelt name still does not pass: step 2
#       refuses any [leanOptions] other than the three pinned options (S5;
#       the scan's rule `options`, which reads the options the build passed,
#       stays as a second line that no change of lakefile.toml alone reaches)
#   (e) a design file that no longer matches the generated Lean file; and the
#       decoy of round 4, issue 4: the header of the design record altered, and a
#       copy generated from the same JSON file under another name
#   (d) a failing build makes check.sh exit non-zero, at the build step, and
#       the error names the file
#   (src) one copy with several modules, each with one defect, and a full list
#       of what the scan and the audit must say about each: a file outside the
#       import closure (c); a declared axiom (f); a scoped instance in plain
#       sight (S3) and one behind `/-/-/` (B2); an indented `variable?` (S4);
#       a tactic configuration that carries a program (M8); a universe
#       parameter; a simp attribute; a notation; a definition of a
#       metaprogramming type; a definition that hides a name of Mathlib; an
#       opaque, an unsafe and a partial definition, an argument with a default
#       value, definitions marked reducible and irreducible (round 4, issue
#       9); file names that the tree rule refuses: a non-ASCII letter, a
#       leading `_`, the extension .LEAN, a symbolic link (round 4, issue 9);
#       and a module that writes a file into scripts/ while it is compiled,
#       which the comparison of the digests at the end reports
#   (stored) a compiled file that was not made from the present sources: a
#       module whose stored axiom list no longer agrees with the declarations
#       it refers to is refused by the audit (round 4, issue 9)
#   (a) a declaration added with the kernel check switched off, as in
#       review/tooling/AuditGapDemo.lean, passes the build and the axiom audit
#       and is rejected by the replay steps: one line for leanchecker on the
#       compiled files, and one line for each tool that checks the export and
#       is installed, which must name its reason. A line says PASS only if the
#       same tool accepted the unmodified copy.
#   (b) the source scan flags that file
#   (pyc) in the same copy, a module of the library in a directory named
#       __pycache__, imported by the root: the scan refuses it, and the record
#       of the run lists its digest (round 4, issue 1)
#   (origin) the audit refuses compiled files of the library that are loaded
#       from another directory than .lake/build of the project
#   (m9) when lean fails in the audit program after the audit has printed its
#       result, check.sh shows the error (M9)
#   (s6) --quick says how the last full run on the present files ended (S6);
#       for that run the compiled configuration of a dependency in .lake/config
#       is replaced by a file that is not one, which --quick must not read
#       (qcfg; round 4, issue 5)
#   (g) what the export checkers start from: with the declaration of Eq
#       removed from a small export, four of them refuse it, each with its
#       message about Eq, and con-leche and con-ron accept it (M7)
#   and two sets of small cases for the source scan and for the design
#   generator (scripts/selftest_static.py).
#
# SELFTEST_KEEP=1 keeps the temporary directory and prints its path.
# SELFTEST_ONLY="<tags>" runs only the named groups of controls (static, control,
# s6, cfg, b1, s5, e, d, src, stored, origin, m9, bypass, g), for work on this script; the
# copies are then made from the build products of this checkout when the positive control is
# not among them, and the last line says that the self-test was partial.
set -u

# an environment of its own, as scripts/check.sh gives itself
case "${1:-}" in
  --clean-environment) shift ;;
  *)
    exec env -i HOME="${HOME:-}" PATH="${PATH:-/usr/bin:/bin}" TMPDIR="${TMPDIR:-/tmp}" \
      LC_ALL=C PYTHONUTF8=1 PYTHONIOENCODING=utf-8 PYTHONDONTWRITEBYTECODE=1 \
      PYTHONSAFEPATH=1 PYTHONNOUSERSITE=1 \
      LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true LAKE_CONFIG=/nonexistent/lake-config.toml \
      CHECK_REPLAY_JOBS="${CHECK_REPLAY_JOBS:-1}" CHECK_SCAN_JOBS="${CHECK_SCAN_JOBS:-2}" \
      CHECK_BUILD_JOBS="${CHECK_BUILD_JOBS:-}" SELFTEST_KEEP="${SELFTEST_KEEP:-0}" \
      SELFTEST_ONLY="${SELFTEST_ONLY:-}" \
      sh "$0" --clean-environment "$@" ;;
esac
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
# Python imports no module from the project directory (PYTHONSAFEPATH=1, Python 3.11 or later)
if ! python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) and sys.flags.safe_path and sys.flags.no_user_site else 1)' >/dev/null 2>&1; then
  echo "selftest.sh: needs python3 through PATH, version 3.11 or later (an older one ignores PYTHONSAFEPATH=1)" >&2
  exit 2
fi
LIBRARY=VoltageToBit

TMP="$(mktemp -d "${TMPDIR:-/tmp}/vtb-selftest.XXXXXX")" || exit 2
cleanup() {
  if [ "${SELFTEST_KEEP:-0}" = 1 ]; then echo "kept: $TMP"; else rm -rf "$TMP"; fi
}
trap cleanup EXIT
trap 'exit 130' INT TERM

STATUS=0
# want <tag>: is this group of controls to be run?
want() { case " ${SELFTEST_ONLY:-$1} " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
BASE=checkout      # where the copies take their build products from
# The kind of the controls that follow (set with `kind`): negative, positive, observation or
# checkout. The PASS lines of each kind are counted for the last line.
KIND=negative; N_NEGATIVE=0; N_POSITIVE=0; N_OBSERVATION=0; N_CHECKOUT=0; N_FAIL=0
kind() { KIND="$1"; }
pass() {
  echo "PASS $1"
  case "$KIND" in
    negative) N_NEGATIVE=$((N_NEGATIVE + 1)) ;;
    positive) N_POSITIVE=$((N_POSITIVE + 1)) ;;
    observation) N_OBSERVATION=$((N_OBSERVATION + 1)) ;;
    checkout) N_CHECKOUT=$((N_CHECKOUT + 1)) ;;
  esac
}
flunk() { echo "FAIL $1"; STATUS=1; N_FAIL=$((N_FAIL + 1)); }
show_tail() { tail -n 8 "$1" | cut -c1-300 | sed 's/^/         /'; }
# verdict <description> <log> <pattern>...: PASS if every fixed string occurs in the log
verdict() {
  v_what="$1"; v_log="$2"; shift 2
  v_missing=""
  for v_pattern in "$@"; do
    if ! grep -q -F -- "$v_pattern" "$v_log"; then v_missing="$v_missing [$v_pattern]"; fi
  done
  if [ -z "$v_missing" ]; then
    pass "$v_what"
  else
    flunk "$v_what"
    echo "       not found in the output of check.sh:$v_missing"
    echo "       last lines of that output:"
    show_tail "$v_log"
  fi
}
present() { grep -q -F -- "$2" "$1"; }   # present <log> <fixed string>
absent() { ! grep -q -F -- "$2" "$1"; }

tree_digest() {   # one hash over every file of this checkout that a control could have touched
  # (in every directory, whatever its name; Python's __pycache__ is passed over under scripts/ only)
  python3 -c 'import hashlib, pathlib
h = hashlib.sha256()
roots = ["VoltageToBit.lean", "VoltageToBit", "designs", "scripts", "evidence", "lakefile.toml",
         "lake-manifest.json", "lean-toolchain"]
files = []
for root in roots:
    path = pathlib.Path(root)
    files += [path] if path.is_file() else [p for p in path.rglob("*") if p.is_file()]
for path in sorted(files, key=lambda p: p.as_posix()):
    if path.parts[0] == "scripts" and "__pycache__" in path.parts:
        continue
    h.update(path.as_posix().encode() + b"\0" + hashlib.sha256(path.read_bytes()).digest())
print(h.hexdigest())'
}
BEFORE="$(tree_digest)"

if [ ! -d .lake/build/lib ]; then
  echo "selftest.sh: no build products in .lake/build; run scripts/check.sh first" >&2
  exit 2
fi
PACKAGES="$(cd .lake/packages && pwd -P)" || exit 2

# copy_project <name> <from>: a throwaway copy in $TMP/<name>. <from> is `none` (no build
# products: the first build in the copy compiles everything), `checkout` (the build products
# of this checkout) or the name of another copy (its build products)
copy_project() {
  c_dir="$TMP/$1"
  mkdir -p "$c_dir/.lake"
  cp -R "$LIBRARY" "$LIBRARY.lean" scripts designs lakefile.toml lake-manifest.json lean-toolchain "$c_dir/"
  rm -rf "$c_dir/scripts/__pycache__"
  case "$2" in
    none) ;;
    checkout) cp -R .lake/build "$c_dir/.lake/build" ;;
    *) cp -R "$TMP/$2/.lake/build" "$c_dir/.lake/build" ;;
  esac
  ln -s "$PACKAGES" "$c_dir/.lake/packages"
}
add_module() {     # add_module <copy> <Name> <imported: yes|no>; the Lean text is read from standard input
  mkdir -p "$TMP/$1/$LIBRARY/Selftest"
  cat >"$TMP/$1/$LIBRARY/Selftest/$2.lean"
  if [ "$3" = yes ]; then
    printf 'import %s.Selftest.%s\n' "$LIBRARY" "$2" >>"$TMP/$1/$LIBRARY.lean"
  fi
}
run_check() {      # run_check <copy> <options>...: output in $TMP/<copy>.log, exit status in CHECK_STATUS
  r_copy="$1"; shift
  (cd "$TMP/$r_copy" && sh scripts/check.sh "$@") >"$TMP/$r_copy.log" 2>&1
  CHECK_STATUS=$?
  LOG="$TMP/$r_copy.log"
}
repin() {          # repin <copy>: make the copy's pin accept its present configuration files
  (cd "$TMP/$1" && python3 -c 'import hashlib
names = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]
with open("scripts/pinned-config.sha256", "w", encoding="utf-8") as out:
    for n in names:
        out.write(hashlib.sha256(open(n, "rb").read()).hexdigest() + "  " + n + "\n")')
}
# A Mathlib module that the library itself imports: compiled already, so a control may import it.
MATHLIB_IMPORT="$(grep -h -E '^import Mathlib\.[A-Za-z0-9_.]+$' $(find "$LIBRARY" -name '*.lean' | LC_ALL=C sort) | head -n 1 | sed 's/^import //')"
# compiled <module>: is the module of Mathlib compiled in the linked packages?
compiled() { [ -f "$PACKAGES/mathlib/.lake/build/lib/lean/$(printf '%s' "$1" | tr . /).olean" ]; }
if [ -z "$MATHLIB_IMPORT" ] || ! compiled "$MATHLIB_IMPORT"; then
  echo "selftest.sh: the library imports no compiled module of Mathlib directly; update the controls" >&2
  exit 2
fi
# A file of the library to which a control can append: the first one, in sorted order, that
# is not generated from a design file.
VICTIM="$(grep -L '^GENERATED by scripts/gen_design.py' $(find "$LIBRARY" -name '*.lean' | LC_ALL=C sort) | head -n 1)"

# ---------------------------------------------------------------------------
if want static; then
echo "== small cases for the source scan and for the design generator =="
python3 -B scripts/selftest_static.py "$ROOT" "$TMP/static" >"$TMP/static.out" 2>&1 || STATUS=1
cat "$TMP/static.out"
# each of its lines is a negative control with positive cases inside it
N_NEGATIVE=$((N_NEGATIVE + $(grep -c '^PASS ' "$TMP/static.out")))
N_FAIL=$((N_FAIL + $(grep -c '^FAIL ' "$TMP/static.out")))
fi

# ---------------------------------------------------------------------------
: >"$TMP/export-tools.txt"
CONTROL="$TMP/control-full.log"
: >"$CONTROL"
if want control; then
echo "== positive control: a copy without build products (a full run of check.sh) =="
BASE=control
copy_project control none
# (py) Python modules planted in the top directory of the copy, which is check.sh's working
# directory: a program that imported one of them instead of the standard module would leave a
# mark and stop with exit status 3
for planted in hashlib json; do
  cat >"$TMP/control/$planted.py" <<'EOF'
# Planted by scripts/selftest.sh, control (py): a Python program that imports this file
# instead of the module of the standard library leaves a mark and stops with exit status 3.
import sys
open(__file__ + ".imported", "a").close()
sys.exit(3)
EOF
done
run_check control
cp "$LOG" "$CONTROL"
kind positive
if [ "$CHECK_STATUS" = 0 ]; then
  verdict "control: a copy of the project without any build product passes a full run of check.sh, which compiles every module" "$CONTROL" \
    "RESULT design-record: ok" "RESULT config: ok" "RESULT build: ok" "RESULT source-scan: ok" \
    "RESULT axiom-audit: ok" "RESULT import-closure: ok" "RESULT declaration-count: ok" \
    "RESULT replay-modules: ok" "PASSED. Compiled: all " "Kernel replay: (1) the compiled files of the"
else
  flunk "control: a copy of the project without any build product passes a full run of check.sh (exit status $CHECK_STATUS)"
  show_tail "$CONTROL"
fi
DIFFER=""
for record in sources.sha256 versions.txt source-scan.txt audit.txt kernel-replay.txt; do
  cmp -s "evidence/lean/$record" "$TMP/control/evidence/lean/$record" || DIFFER="$DIFFER $record"
done
if [ -z "$DIFFER" ]; then
  pass "control: the records that run wrote (sources.sha256, versions.txt, source-scan.txt, audit.txt, kernel-replay.txt) are byte for byte those in evidence/lean/ of this checkout"
else
  flunk "control: records in evidence/lean/ of this checkout are not what a full run of check.sh writes for an unmodified copy:$DIFFER (run scripts/check.sh, without --whole-env, to bring them up to date)"
fi
kind negative
if [ "$CHECK_STATUS" = 0 ] && [ -z "$DIFFER" ] && [ ! -e "$TMP/control/hashlib.py.imported" ] && [ ! -e "$TMP/control/json.py.imported" ]; then
  pass "(py) that copy has a hashlib.py and a json.py in its top directory, check.sh's working directory, which end any Python program that imports them (round 4, issue 2): no program imported them, the run passed, and its records are those of this checkout"
else
  flunk "(py) a hashlib.py or a json.py in the top directory of the copy was imported ($(ls "$TMP/control/"*.imported 2>/dev/null | sed 's|.*/||' | tr '\n' ' ')), or the run of the copy failed or wrote other records"
fi
grep '^RESULT replay-export/' "$CONTROL" | sed 's|^RESULT replay-export/||; s|:.*||' >"$TMP/export-tools.txt"
grep '^RESULT .*: NOT RUN' "$CONTROL" | sed 's/^/     note: /'
fi

# ---------------------------------------------------------------------------
if want s6 && [ "$BASE" != control ]; then
  flunk "(s6) these controls need the positive control: name both in SELFTEST_ONLY"
elif want s6; then
echo "== (s6) --quick says how the last full run on these files ended =="
# (qcfg) the compiled configuration of a dependency that the full run left in .lake/config,
# replaced by a file that is not one, its trace left as it is (round 4, issue 5): Lake would read
# it, and fail, if --quick did not remove .lake/config
PLANTED_CONFIG="$(ls "$TMP/control/.lake/config/"*/lakefile.olean 2>/dev/null | head -n 1)"
if [ -n "$PLANTED_CONFIG" ]; then printf 'not a compiled configuration\n' >"$PLANTED_CONFIG"; fi
run_check control --quick
kind negative
if [ -z "$PLANTED_CONFIG" ]; then
  flunk "(qcfg) the copy of the positive control has no compiled configuration in .lake/config; update this control"
elif [ "$CHECK_STATUS" = 0 ] && present "$LOG" "removing .lake/config" && present "$LOG" "RESULT build: ok"; then
  pass "(qcfg) a compiled configuration of a dependency in .lake/config replaced by a file that is not one (round 4, issue 5): --quick removes .lake/config before the build, and the build passes"
else
  flunk "(qcfg) with a file that is not a compiled configuration in .lake/config: exit status $CHECK_STATUS, or --quick did not remove .lake/config, or the build failed"
  show_tail "$LOG"
fi
kind positive
if [ "$CHECK_STATUS" = 0 ]; then
  verdict "(s6) --quick after a full run that passed: it passes, removes .lake/config, compiles nothing again, and says that the record names these same files and says that its run passed" "$LOG" \
    "RESULT import-closure: ok" "0 compiled in this run, the others reused" "removing .lake/config" \
    "names these same files (by the digest of their list) and says that its run PASSED;" \
    "QUICK CHECK PASSED (steps 1 to 6)." "no declaration was re-checked by any kernel in this run"
else
  flunk "(s6) --quick on the unmodified copy after its full run: exit status $CHECK_STATUS"
  show_tail "$LOG"
fi
kind negative
# the same record, as a full run that failed at the kernel replay would have left it
sed 's/^  outcome of the run of scripts\/check.sh that wrote this record: every step that was run passed\.$/  outcome of the run of scripts\/check.sh that wrote this record: FAILED: replay-modules/' \
  "$TMP/control/evidence/lean/kernel-replay.txt" >"$TMP/failed-record.txt"
if cmp -s "$TMP/failed-record.txt" "$TMP/control/evidence/lean/kernel-replay.txt"; then
  flunk "(s6) the record has no outcome line of the expected form; update this control"
else
  cp "$TMP/failed-record.txt" "$TMP/control/evidence/lean/kernel-replay.txt"
  run_check control --quick
  if [ "$CHECK_STATUS" = 0 ] && absent "$LOG" "its run PASSED"; then
    verdict "(s6) --quick when the record of the last full run on these files says FAILED: the line that reports the quick check says so" "$LOG" \
      "names these same files (by the digest of their list) and says that its run FAILED: replay-modules;" \
      "QUICK CHECK PASSED (steps 1 to 6)."
    tail -n 1 "$LOG" | grep -q -F "says that its run FAILED: replay-modules;" \
      || flunk "(s6) the last line of --quick does not say that the last full run failed"
  else
    flunk "(s6) --quick with a record that says FAILED: exit status $CHECK_STATUS, or it still says that the run passed"
    show_tail "$LOG"
  fi
fi
fi

# ---------------------------------------------------------------------------
if want cfg; then
echo "== (cfg) a build configuration that is not the pinned one =="
# A copy without .lake, and a PATH without Lean: if the configuration check let one of these
# through, no Lean tool could be started on it.
SAFE_PATH="$(dirname "$(command -v python3)"):/usr/bin:/bin"
if (PATH="$SAFE_PATH"; command -v lake >/dev/null 2>&1 || command -v lean >/dev/null 2>&1); then
  flunk "(cfg) cannot make a PATH with python3 and without lake and lean; these controls were not run"
else
  mkdir -p "$TMP/cfg"
  cp -R "$LIBRARY" "$LIBRARY.lean" scripts designs lakefile.toml lake-manifest.json lean-toolchain "$TMP/cfg/"
  rm -rf "$TMP/cfg/scripts/__pycache__"
  # edit_text <file> <python expression>: map the text `t` of <file> in the copy to the value of
  # the expression; exit status 3 if that changes nothing
  edit_text() {
    (cd "$TMP/cfg" && python3 -c 'import sys
name, edit = sys.argv[1], sys.argv[2]
t = open(name, encoding="utf-8", newline="").read()
new = eval(edit)
if new == t:
    sys.exit(3)
open(name, "w", encoding="utf-8", newline="").write(new)' "$1" "$2")
  }
  # the unchanged configuration passes step 2's comparison; the copy has no dependencies
  (cd "$TMP/cfg" && PATH="$SAFE_PATH" sh scripts/check.sh --quick) >"$TMP/cfg.log" 2>&1
  c_status=$?
  cp "$TMP/cfg.log" "$TMP/cfg-unchanged.log"
  kind positive
  if [ "$c_status" = 1 ] && present "$TMP/cfg.log" "pinned: lakefile.toml" && present "$TMP/cfg.log" "pinned: lake-manifest.json" \
      && present "$TMP/cfg.log" "pinned: lean-toolchain" && absent "$TMP/cfg.log" "NOT THE PINNED FILE" \
      && absent "$TMP/cfg.log" "NOT ALLOWED" && present "$TMP/cfg.log" "NOT READY: .lake/packages/mathlib is missing" \
      && present "$TMP/cfg.log" "CHECK FAILED: config" && absent "$TMP/cfg.log" "== 3."; then
    pass "(cfg) the unchanged configuration files are accepted as the pinned ones, with no key refused; in a copy without the dependencies check.sh then stops at step config and says that .lake/packages/mathlib is missing"
  else
    flunk "(cfg) the unchanged configuration files are not accepted, or a copy without dependencies did not stop at step config (exit status $c_status)"
    show_tail "$TMP/cfg.log"
  fi
  kind negative
  # name | file | what must be reported | python expression that maps the text `t` of the file to the changed text
  while IFS='|' read -r c_name c_file c_expect c_edit; do
    [ -n "$c_name" ] || continue
    if [ "$c_file" = lakefile.lean ]; then
      : >"$TMP/cfg/lakefile.lean"
    else
      cp "$c_file" "$TMP/cfg/$c_file"
      edit_text "$c_file" "$c_edit"
      if [ $? != 0 ]; then
        flunk "(cfg) $c_name: the file does not have the text this control changes; update the control"
        cp "$c_file" "$TMP/cfg/$c_file"
        continue
      fi
    fi
    (cd "$TMP/cfg" && PATH="$SAFE_PATH" sh scripts/check.sh --quick --keep-going) </dev/null >"$TMP/cfg.log" 2>&1
    c_status=$?
    if [ "$c_status" = 1 ] && present "$TMP/cfg.log" "$c_expect" && present "$TMP/cfg.log" "RESULT config: FAILED (the build configuration is not the pinned one" \
        && present "$TMP/cfg.log" "CHECK FAILED: config" && absent "$TMP/cfg.log" "RESULT build:" && absent "$TMP/cfg.log" "== 3."; then
      pass "(cfg) $c_name: check.sh stops at step config, also with --keep-going, and reports: $c_expect"
    else
      flunk "(cfg) $c_name: exit status $c_status, or step config did not report \"$c_expect\", or check.sh went on"
      show_tail "$TMP/cfg.log"
    fi
    if [ "$c_file" = lakefile.lean ]; then rm -f "$TMP/cfg/lakefile.lean"; else cp "$c_file" "$TMP/cfg/$c_file"; fi
  done <<'EOF'
lakefile.toml without the line defaultTargets (B1)|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|"".join(l for l in t.splitlines(True) if not l.startswith("defaultTargets"))
lakefile.toml with another default target and a second library (B1)|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t.replace('defaultTargets = ["VoltageToBit"]', 'defaultTargets = ["Other"]') + '\n[[lean_lib]]\nname = "Other"\n'
lakefile.toml without autoImplicit = false and relaxedAutoImplicit = false (S5)|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|"".join(l for l in t.splitlines(True) if "utoImplicit" not in l)
lakefile.toml with autoImplicit = true|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t.replace("\nautoImplicit = false", "\nautoImplicit = true")
lakefile.toml with an option that switches the kernel check off|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t.replace("[leanOptions]\n", "[leanOptions]\ndebug.skipKernelTC = true\n")
lakefile.toml with extra arguments for the compiler|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t + 'moreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n'
lakefile.toml with another revision of Mathlib|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t.replace('rev = "', 'rev = "x')
lakefile.toml with a second dependency|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t + '\n[[require]]\nname = "other"\npath = "../other"\n'
lakefile.toml with a comment added|lakefile.toml|NOT THE PINNED FILE: lakefile.toml|t + "# a comment\n"
lake-manifest.json with another revision of Mathlib|lake-manifest.json|NOT THE PINNED FILE: lake-manifest.json|t.replace('"rev": "', '"rev": "0', 1)
lean-toolchain naming another toolchain|lean-toolchain|NOT THE PINNED FILE: lean-toolchain|t.strip() + "-rc1\n"
a lakefile.lean next to lakefile.toml|lakefile.lean|NOT ALLOWED: lakefile.lean|
EOF
  # The same kind of change with the pin changed to accept the file (round 4, issue 3): a key that
  # or an option that could move the library's sources or build products, or reach the compiler, is refused
  # whatever the pin says. srcDir under [[lean_lib]] made Lake compile the library from another
  # directory than the one the scan and the digests read.
  # name | what must be reported | python expression that maps the text `t` of lakefile.toml to the changed text
  while IFS='|' read -r c_name c_expect c_edit; do
    [ -n "$c_name" ] || continue
    cp lakefile.toml "$TMP/cfg/lakefile.toml"
    if ! edit_text lakefile.toml "$c_edit"; then
      flunk "(cfg) $c_name: lakefile.toml does not have the text this control changes; update the control"
      continue
    fi
    repin cfg
    (cd "$TMP/cfg" && PATH="$SAFE_PATH" sh scripts/check.sh --quick --keep-going) </dev/null >"$TMP/cfg.log" 2>&1
    c_status=$?
    if [ "$c_status" = 1 ] && present "$TMP/cfg.log" "$c_expect" && present "$TMP/cfg.log" "pinned: lakefile.toml" \
        && absent "$TMP/cfg.log" "NOT THE PINNED FILE" && present "$TMP/cfg.log" "RESULT config: FAILED (the build configuration" \
        && present "$TMP/cfg.log" "CHECK FAILED: config" && absent "$TMP/cfg.log" "RESULT build:" && absent "$TMP/cfg.log" "== 3."; then
      pass "(cfg) $c_name, with the pin changed to accept the file: check.sh stops at step config, also with --keep-going, and reports: $c_expect"
    else
      flunk "(cfg) $c_name, with the pin changed to accept the file: exit status $c_status, or step config did not report \"$c_expect\", or check.sh went on"
      show_tail "$TMP/cfg.log"
    fi
    cp lakefile.toml "$TMP/cfg/lakefile.toml"
    cp scripts/pinned-config.sha256 "$TMP/cfg/scripts/pinned-config.sha256"
  done <<'EOF'
lakefile.toml with srcDir in [[lean_lib]] (round 4, issue 3)|NOT ALLOWED: lakefile.toml has the key srcDir in [[lean_lib]] "VoltageToBit"; accepted there: name|t + 'srcDir = "alt"\n'
lakefile.toml with roots in [[lean_lib]]|NOT ALLOWED: lakefile.toml has the key roots in [[lean_lib]] "VoltageToBit"|t + 'roots = ["VoltageToBit", "Other"]\n'
lakefile.toml with globs in [[lean_lib]]|NOT ALLOWED: lakefile.toml has the key globs in [[lean_lib]] "VoltageToBit"|t + 'globs = ["VoltageToBit.+"]\n'
lakefile.toml with libName in [[lean_lib]]|NOT ALLOWED: lakefile.toml has the key libName in [[lean_lib]] "VoltageToBit"|t + 'libName = "Other"\n'
lakefile.toml with moreLeanArgs in [[lean_lib]]|NOT ALLOWED: lakefile.toml has the key moreLeanArgs in [[lean_lib]] "VoltageToBit"|t + 'moreLeanArgs = ["-DautoImplicit=true"]\n'
lakefile.toml with weakLeanArgs in [[lean_lib]]|NOT ALLOWED: lakefile.toml has the key weakLeanArgs in [[lean_lib]] "VoltageToBit"|t + 'weakLeanArgs = ["-DautoImplicit=true"]\n'
lakefile.toml with options of its own in [[lean_lib]]|NOT ALLOWED: lakefile.toml has the key leanOptions in [[lean_lib]] "VoltageToBit"|t + '\n[lean_lib.leanOptions]\nautoImplicit = true\n'
lakefile.toml with srcDir in the package table|NOT ALLOWED: lakefile.toml has the key srcDir in its package table|t.replace("[leanOptions]", 'srcDir = "alt"\n\n[leanOptions]', 1)
lakefile.toml with buildDir in the package table|NOT ALLOWED: lakefile.toml has the key buildDir in its package table|t.replace("[leanOptions]", 'buildDir = "other"\n\n[leanOptions]', 1)
lakefile.toml with moreLeanArgs in the package table|NOT ALLOWED: lakefile.toml has the key moreLeanArgs in its package table|t.replace("[leanOptions]", 'moreLeanArgs = ["-DautoImplicit=true"]\n\n[leanOptions]', 1)
lakefile.toml with an executable|NOT ALLOWED: lakefile.toml has the key lean_exe in its package table|t + '\n[[lean_exe]]\nname = "x"\nroot = "Main"\n'
lakefile.toml with subDir in [[require]]|NOT ALLOWED: lakefile.toml has the key subDir in [[require]] "mathlib"|t.replace('rev = "v4.35.0"', 'rev = "v4.35.0"\nsubDir = "x"', 1)
lakefile.toml with a second library of the same name|NOT ALLOWED: lakefile.toml must have exactly one [[lean_lib]] named VoltageToBit; it has 2|t + '\n[[lean_lib]]\nname = "VoltageToBit"\n'
lakefile.toml with an option that changes what a statement means (round 5)|NOT ALLOWED: lakefile.toml: [leanOptions] must be exactly pp.unicode.fun = true, autoImplicit = false and relaxedAutoImplicit = false|t.replace("relaxedAutoImplicit = false", "relaxedAutoImplicit = false\ndeprecated.oldSectionVars = true", 1)
lakefile.toml with autoImplicit switched on in [leanOptions]|NOT ALLOWED: lakefile.toml: [leanOptions] must be exactly|t.replace("autoImplicit = false\nrelaxed", "autoImplicit = true\nrelaxed", 1)
lakefile.toml with autoImplicit = 0, which Python counts as false|NOT ALLOWED: lakefile.toml: [leanOptions] must be exactly|t.replace("autoImplicit = false\nrelaxed", "autoImplicit = 0\nrelaxed", 1)
EOF

  echo "== (env) the environment that check.sh gives itself =="
  # check.sh's own list is selftest.sh's list without SELFTEST_* and with LEAN_ABORT_ON_PANIC=1
  # (round 4, issue 9: the environment check was not exercised)
  (cd "$TMP/cfg" && env -u SELFTEST_KEEP -u SELFTEST_ONLY LEAN_ABORT_ON_PANIC=1 PATH="$SAFE_PATH" \
    sh scripts/check.sh --clean-environment --quick) >"$TMP/env.log" 2>&1
  c_status=$?
  kind positive
  if [ "$c_status" = 1 ] && absent "$TMP/env.log" "the environment is not the one" && present "$TMP/env.log" "RESULT design-record: ok" \
      && present "$TMP/env.log" "NOT READY: .lake/packages/mathlib is missing"; then
    pass "(env) check.sh called with --clean-environment and exactly the environment it gives itself: it runs (and stops at step config in the copy without dependencies)"
  else
    flunk "(env) check.sh called with exactly the environment it gives itself: exit status $c_status, or it did not run"
    show_tail "$TMP/env.log"
  fi
  kind negative
  (cd "$TMP/cfg" && env -u SELFTEST_KEEP -u SELFTEST_ONLY LEAN_ABORT_ON_PANIC=1 LEAN_PATH=/nonexistent PATH="$SAFE_PATH" \
    sh scripts/check.sh --clean-environment --quick) >"$TMP/env.log" 2>&1
  c_status=$?
  if [ "$c_status" = 2 ] && present "$TMP/env.log" "the environment is not the one this script gives itself" \
      && present "$TMP/env.log" "Variables it did not ask for: LEAN_PATH." && absent "$TMP/env.log" "== 1."; then
    pass "(env) the same with LEAN_PATH added: check.sh stops with exit status 2 before step 1 and names the variable"
  else
    flunk "(env) the same with LEAN_PATH added: exit status $c_status, or the variable was not named, or a step ran"
    show_tail "$TMP/env.log"
  fi
  (cd "$TMP/cfg" && env -u SELFTEST_KEEP -u SELFTEST_ONLY -u PYTHONSAFEPATH LEAN_ABORT_ON_PANIC=1 PATH="$SAFE_PATH" \
    sh scripts/check.sh --clean-environment --quick) >"$TMP/env.log" 2>&1
  c_status=$?
  if [ "$c_status" = 2 ] && present "$TMP/env.log" "Not set as the script sets them: PYTHONSAFEPATH." && absent "$TMP/env.log" "== 1."; then
    pass "(env) the same without PYTHONSAFEPATH (round 4, issue 2): check.sh stops with exit status 2 before step 1 and names the variable"
  else
    flunk "(env) the same without PYTHONSAFEPATH: exit status $c_status, or the variable was not named, or a step ran"
    show_tail "$TMP/env.log"
  fi
  # a python3 that fails the test of version and safe path, as one older than 3.11 does
  mkdir -p "$TMP/oldpython"
  printf '#!/bin/sh\nexit 1\n' >"$TMP/oldpython/python3"
  chmod +x "$TMP/oldpython/python3"
  (cd "$TMP/cfg" && PATH="$TMP/oldpython:$SAFE_PATH" sh scripts/check.sh --quick) >"$TMP/env.log" 2>&1
  c_status=$?
  if [ "$c_status" = 2 ] && present "$TMP/env.log" "check.sh: needs python3 through PATH, version 3.11 or later" && absent "$TMP/env.log" "== 1."; then
    pass "(env) a python3 that fails the test for version 3.11 and the safe path (a stand-in): check.sh stops with exit status 2 before step 1"
  else
    flunk "(env) a python3 that fails the test for version 3.11 and the safe path: exit status $c_status, or a step ran"
    show_tail "$TMP/env.log"
  fi
  # variables of the caller are dropped: the run is the one of the unchanged configuration above
  mkdir -p "$TMP/pypath"
  printf 'import sys\nopen(__file__ + ".imported", "a").close()\nsys.exit(3)\n' >"$TMP/pypath/json.py"
  (cd "$TMP/cfg" && env LEAN_PATH=/nonexistent LAKE_HOME=/nonexistent ELAN_TOOLCHAIN=none PYTHONPATH="$TMP/pypath" \
    PATH="$SAFE_PATH" sh scripts/check.sh --quick) >"$TMP/env.log" 2>&1
  c_status=$?
  if [ "$c_status" = 1 ] && [ ! -e "$TMP/pypath/json.py.imported" ] \
      && [ "$(grep -v '^elapsed: ' "$TMP/env.log")" = "$(grep -v '^elapsed: ' "$TMP/cfg-unchanged.log")" ]; then
    pass "(env) a call with LEAN_PATH, LAKE_HOME, ELAN_TOOLCHAIN and PYTHONPATH set (PYTHONPATH with a json.py that ends any program importing it): the output is the one without them"
  else
    flunk "(env) a call with variables of the caller: exit status $c_status, or json.py was imported, or the output differs from the one without them"
    show_tail "$TMP/env.log"
  fi
fi
fi

# ---------------------------------------------------------------------------
if want b1; then
echo "== (b1) sources that do not compile, with compiled files of an earlier build present =="
# The pin of the copy is changed to accept its lakefile, as a deliberate change would do: then
# only the build step stands between the stale compiled files and the audit.
b1_control() {     # b1_control <copy> <description>
  printf '\ntheorem %s.Selftest.broken : (1 : Nat) = 2 := rfl\n' "$LIBRARY" >>"$TMP/$1/$VICTIM"
  repin "$1"
  run_check "$1" --quick
  if [ "$CHECK_STATUS" = 1 ] && absent "$LOG" "RESULT axiom-audit:" && absent "$LOG" "RESULT source-scan: ok"; then
    verdict "(b1) $2: check.sh builds the library by name, the changed file is compiled again and fails, and check.sh stops at step build" \
      "$LOG" "RESULT config: ok" "$VICTIM:" "RESULT build: FAILED (lake build $LIBRARY exited with status" "CHECK FAILED: build"
  else
    flunk "(b1) $2: exit status $CHECK_STATUS, or check.sh went on after the failure"
    show_tail "$LOG"
  fi
}
if [ -z "$VICTIM" ]; then
  flunk "(b1) the library has no file that is not generated; update this control"
else
  copy_project b1a "$BASE"
  grep -v '^defaultTargets' lakefile.toml >"$TMP/b1a/lakefile.toml"
  if cmp -s lakefile.toml "$TMP/b1a/lakefile.toml"; then
    flunk "(b1) lakefile.toml has no line defaultTargets; update this control"
  else
    b1_control b1a "a file that no longer compiles, lakefile.toml without default targets"
  fi
  copy_project b1b "$BASE"
  sed 's/^defaultTargets = .*$/defaultTargets = ["Other"]/' lakefile.toml >"$TMP/b1b/lakefile.toml"
  printf '\n[[lean_lib]]\nname = "Other"\n' >>"$TMP/b1b/lakefile.toml"
  : >"$TMP/b1b/Other.lean"
  b1_control b1b "a file that no longer compiles, lakefile.toml with another default target"
fi
fi

# ---------------------------------------------------------------------------
if want s5; then
echo "== (s5) lakefile.toml without autoImplicit = false, and names that are bound nowhere =="
# As in (b1), the pin of the copy is changed to accept its lakefile: then the scan and the audit
# are what stands between a misspelt name and a theorem about an arbitrary variable.
copy_project s5 "$BASE"
grep -v 'utoImplicit' lakefile.toml >"$TMP/s5/lakefile.toml"
if cmp -s lakefile.toml "$TMP/s5/lakefile.toml"; then
  flunk "(s5) lakefile.toml has no autoImplicit lines; update this control"
else
  repin s5
  add_module s5 Auto yes <<'EOF'
namespace VoltageToBit.Selftest

theorem thresholds_agree (h : VDDmin = VDDmxa) : VDDmxa = VDDmin := h.symm

theorem concrete_one (h : n + 0 = 1) : n = 1 := h

end VoltageToBit.Selftest
EOF
  run_check s5 --quick --keep-going
  # Since round 5 step 2 refuses any [leanOptions] other than the three pinned options, whatever
  # the pin says, so the copy stops there, before anything is compiled. (The scan's rule
  # `options` stays as a second line behind it; no change of lakefile.toml alone reaches it now.)
  if [ "$CHECK_STATUS" = 1 ] && present "$LOG" "pinned: lakefile.toml" && absent "$LOG" "NOT THE PINNED FILE" \
      && absent "$LOG" "RESULT build:" && absent "$LOG" "== 3."; then
    verdict "(s5) lakefile.toml without the autoImplicit lines, the pin changed to accept it, and two statements with names that are bound nowhere: check.sh stops at step config, before the build, because [leanOptions] is not the pinned set" "$LOG" \
      "NOT ALLOWED: lakefile.toml: [leanOptions] must be exactly pp.unicode.fun = true, autoImplicit = false and relaxedAutoImplicit = false" \
      "CHECK FAILED: config"
  else
    flunk "(s5) the copy was not stopped at step config: exit status $CHECK_STATUS, or check.sh went on to the build"
    show_tail "$LOG"
  fi
fi
fi

# ---------------------------------------------------------------------------
if want e; then
echo "== (e) stale design record =="
copy_project stale "$BASE"
sed 's/"eps": "2"/"eps": "2.5"/' designs/illustrative-1v8.json >"$TMP/stale/designs/illustrative-1v8.json"
if cmp -s designs/illustrative-1v8.json "$TMP/stale/designs/illustrative-1v8.json"; then
  flunk "(e) stale design record: the design file could not be changed; update this control"
else
  run_check stale --quick
  if [ "$CHECK_STATUS" = 1 ] && absent "$LOG" "RESULT config:"; then
    verdict "(e) a design file that differs from the generated Lean file: check.sh stops with exit status 1 at step design-record" \
      "$LOG" "STALE: $LIBRARY/Examples/IllustrativeDesign.lean is not what designs/illustrative-1v8.json generates" \
      "RESULT design-record: FAILED" "CHECK FAILED: design-record"
  else
    flunk "(e) stale design record: exit status $CHECK_STATUS, or check.sh went on after the failure"
    show_tail "$LOG"
  fi
fi
# The decoy of round 4, issue 4: the header of the record that the library uses altered (so that a
# check that went by the header would no longer compare it), its status line changed, and a copy
# generated from the same JSON file under another name, imported by the root
copy_project decoy "$BASE"
RECORD_FILE="$LIBRARY/Examples/IllustrativeDesign.lean"
(cd "$TMP/decoy" && python3 scripts/gen_design.py designs/illustrative-1v8.json "$LIBRARY/Examples/DesignDecoy.lean" illustrativeDecoy) >/dev/null
printf 'import %s.Examples.DesignDecoy\n' "$LIBRARY" >>"$TMP/decoy/$LIBRARY.lean"
sed 's/^GENERATED by /Generated by /; s/^Status: .*$/Status: ALTERED BY THE SELF-TEST./' "$RECORD_FILE" >"$TMP/decoy/$RECORD_FILE"
if cmp -s "$RECORD_FILE" "$TMP/decoy/$RECORD_FILE" || [ ! -f "$TMP/decoy/$LIBRARY/Examples/DesignDecoy.lean" ]; then
  flunk "(e) the decoy: the record could not be altered or the copy could not be generated; update this control"
else
  run_check decoy --quick
  if [ "$CHECK_STATUS" = 1 ] && absent "$LOG" "RESULT config:"; then
    verdict "(e) the decoy of round 4, issue 4: the header of the design record altered and a copy generated under another name: check.sh stops at step design-record and names both files" \
      "$LOG" "STALE: $RECORD_FILE is not what designs/illustrative-1v8.json generates with the definition name illustrative" \
      "NOT LISTED: $LIBRARY/Examples/DesignDecoy.lean begins with the header of a generated design record" \
      "RESULT design-record: FAILED" "CHECK FAILED: design-record"
  else
    flunk "(e) the decoy: exit status $CHECK_STATUS, or check.sh went on after step design-record"
    show_tail "$LOG"
  fi
fi
fi

# ---------------------------------------------------------------------------
if want d; then
echo "== (d) failing build =="
copy_project broken "$BASE"
add_module broken Broken yes <<'EOF'
theorem VoltageToBit.Selftest.broken : (1 : Nat) = 2 := rfl
EOF
run_check broken --quick
if [ "$CHECK_STATUS" = 1 ] && absent "$LOG" "RESULT axiom-audit:" && absent "$LOG" "RESULT source-scan: ok"; then
  verdict "(d) a module that does not compile: check.sh stops with exit status 1 at step build, and the error that it shows names the file" \
    "$LOG" "RESULT config: ok" "error: $LIBRARY/Selftest/Broken.lean:1:" \
    "RESULT build: FAILED (lake build $LIBRARY exited with status" "CHECK FAILED: build"
else
  flunk "(d) failing build: exit status $CHECK_STATUS, or check.sh went on after the failure"
  show_tail "$LOG"
fi
fi

# ---------------------------------------------------------------------------
if want src; then
echo "== (src) defects in the sources, each in a module of its own (one run of check.sh --quick --keep-going) =="
VARIABLE_Q=Mathlib.Tactic.Variable
LINARITH=Mathlib.Tactic.Linarith
if ! compiled "$VARIABLE_Q" || ! compiled "$LINARITH"; then
  flunk "(src) $VARIABLE_Q or $LINARITH is not compiled in the linked packages; update these controls"
else
  copy_project src "$BASE"
  add_module src Orphan no <<'EOF'
theorem VoltageToBit.Selftest.orphan : True := trivial
EOF
  add_module src ExtraAxiom yes <<'EOF'
namespace VoltageToBit.Selftest

axiom selftestAxiom : False

theorem usesIt : (0 : Nat) = 1 := selftestAxiom.elim

end VoltageToBit.Selftest
EOF
  add_module src Scoped yes <<EOF
import $MATHLIB_IMPORT

namespace VoltageToBit.Selftest.Plain

scoped instance fakeLE : LE ℝ := ⟨fun _ _ => True⟩

theorem everything_is_small (x y : ℝ) : x ≤ y := trivial

end VoltageToBit.Selftest.Plain
EOF
  add_module src Hidden yes <<EOF
import $MATHLIB_IMPORT

namespace VoltageToBit.Selftest.Behind

/-/-/
scoped instance fakeLE : LE ℝ := ⟨fun _ _ => True⟩
-- -/ -/

theorem everything_is_small (x y : ℝ) : x ≤ y := trivial

end VoltageToBit.Selftest.Behind
EOF
  add_module src Hyp yes <<EOF
import $VARIABLE_Q

namespace VoltageToBit.Selftest

theorem foo : True := trivial
  variable? [Inhabited Empty]

theorem looksFalse : False := (default : Empty).elim

end VoltageToBit.Selftest
EOF
  add_module src Oracle yes <<EOF
import $LINARITH

namespace VoltageToBit.Selftest

theorem viaOracle (x : Int) (h : 0 < x) : 0 ≤ x := by
  linarith (oracle := { produceCertificate := fun hyps maxVar =>
    Mathlib.Tactic.Linarith.CertificateOracle.simplexAlgorithmSparse.produceCertificate hyps maxVar })

end VoltageToBit.Selftest
EOF
  add_module src Universe yes <<'EOF'
namespace VoltageToBit.Selftest

theorem anySort.{u} (α : Sort u) (x : α) : x = x := rfl

end VoltageToBit.Selftest
EOF
  add_module src Simp yes <<'EOF'
namespace VoltageToBit.Selftest

@[simp] theorem addZero (n : Nat) : n + 0 = n := rfl

end VoltageToBit.Selftest
EOF
  add_module src Meta yes <<EOF
import $MATHLIB_IMPORT

namespace VoltageToBit.Selftest

def piece : Lean.Syntax := default

end VoltageToBit.Selftest
EOF
  add_module src Shadow yes <<EOF
import $MATHLIB_IMPORT

namespace VoltageToBit.Selftest

def Continuous (f : ℝ → ℝ) : Prop := f = f

theorem everything_is_continuous (f : ℝ → ℝ) : Continuous f := rfl

end VoltageToBit.Selftest
EOF
  add_module src Notation yes <<'EOF'
namespace VoltageToBit.Selftest

notation "selftestFalse" => False

theorem usesNotation : selftestFalse → True := fun _ => trivial

end VoltageToBit.Selftest
EOF
  # declarations of the kinds that the audit refuses (round 4, issue 9)
  add_module src Kinds yes <<'EOF'
namespace VoltageToBit.Selftest

opaque hidden : Nat

unsafe def unsafeId (n : Nat) : Nat := n

partial def loop (n : Nat) : Nat := loop (n + 1)

abbrev Small : Type := Nat

@[irreducible] def sealed : Nat := 0

end VoltageToBit.Selftest
EOF
  add_module src Default yes <<'EOF'
namespace VoltageToBit.Selftest

def withDefault (x : optParam Nat 5) : Nat := x

end VoltageToBit.Selftest
EOF
  # a module that writes into scripts/ while it is compiled: the digests taken at the end of
  # the run differ from those taken at its beginning (round 4, issue 9)
  add_module src Writer yes <<'EOF'
#eval (IO.FS.writeFile "scripts/written-while-compiling.txt" "written by a module of the library\n" : IO Unit)
EOF
  # file names that the tree rule refuses, none of them imported (round 4, issue 9); a module
  # in a directory named __pycache__ is in the copy of control (a)
  S="$LIBRARY/Selftest"
  NONASCII="$(printf 'Byp\303\244ss')"
  printf 'theorem VoltageToBit.Selftest.nonAscii : True := trivial\n' >"$TMP/src/$S/$NONASCII.lean"
  printf 'theorem VoltageToBit.Selftest.underscore : True := trivial\n' >"$TMP/src/$S/_Under.lean"
  printf 'theorem VoltageToBit.Selftest.upper : True := trivial\n' >"$TMP/src/$S/Upper.LEAN"
  ln -s Orphan.lean "$TMP/src/$S/Link.lean"
  run_check src --quick --keep-going
  if [ "$CHECK_STATUS" != 1 ] || absent "$LOG" "RESULT build: ok"; then
    flunk "(src) the controls are not valid: check.sh exited with status $CHECK_STATUS, or the copy with the defects did not build"
    show_tail "$LOG"
  else
    verdict "(src) the copy fails at the steps source-scan, axiom-audit, import-closure and declaration-count, and at the comparison of the digests at the end; the build accepts all of it" "$LOG" \
      "RESULT build: ok" "RESULT source-scan: FAILED" "RESULT axiom-audit: FAILED" "RESULT import-closure: FAILED" \
      "RESULT declaration-count: FAILED" "RESULT sources-unchanged: FAILED" \
      "CHECK FAILED: source-scan axiom-audit import-closure declaration-count sources-unchanged"
    verdict "a notation: the scan names the command, the audit names the environment extensions that hold it, and the declarations that Lean made for it are counted in the compiled files and not in the text" "$LOG" \
      "$S/Notation.lean:3:1: [command] a command of kind \`Lean.Parser.Command.notation\` is not on the allow-list" \
      "[extensions] the library has" "RESULT declaration-count: FAILED"
    verdict "(c) a source file that $LIBRARY.lean does not import: the scan and step import-closure name it" "$LOG" \
      "$S/Orphan.lean: [closure] not imported by $LIBRARY.lean" \
      "SOURCE FILE NOT IMPORTED BY $LIBRARY.lean (not built, not audited): $LIBRARY.Selftest.Orphan"
    verdict "(f) an axiom declared and used: the scan names the command, the audit names the axiom and the theorem that depends on it" "$LOG" \
      "$S/ExtraAxiom.lean:3:1: [syntax] syntax of kind \`Lean.Parser.Command.axiom\` is not on the allow-list" \
      "$LIBRARY.Selftest.selftestAxiom: [kinds] declared as axiom" \
      "$LIBRARY.Selftest.usesIt: [axioms] depends on $LIBRARY.Selftest.selftestAxiom"
    verdict "(S3) a scoped instance in plain sight: the scan names the command, the audit names the instance and says that it is scoped" "$LOG" \
      "$S/Scoped.lean:5:1: [syntax] syntax of kind \`Lean.Parser.Command.instance\` is not on the allow-list" \
      "$LIBRARY.Selftest.Plain.fakeLE: [instances] registered as an instance (scoped in $LIBRARY.Selftest.Plain) in $LIBRARY.Selftest.Scoped"
    verdict "(B2) the same instance behind \`/-/-/\`, which Lean reads as a complete comment: the scan reads what Lean reads, and the audit names the instance" "$LOG" \
      "$S/Hidden.lean:6:1: [syntax] syntax of kind \`Lean.Parser.Command.instance\` is not on the allow-list" \
      "$LIBRARY.Selftest.Behind.fakeLE: [instances] registered as an instance (scoped in $LIBRARY.Selftest.Behind) in $LIBRARY.Selftest.Hidden"
    verdict "(S4) an indented \`variable?\` that adds an instance hypothesis: the scan names the command, the audit names the theorem whose text reads \`: False\`" "$LOG" \
      "$S/Hyp.lean:6:3: [command] a command of kind \`Mathlib.Command.Variable.variable?\` is not on the allow-list" \
      "$LIBRARY.Selftest.looksFalse: [binders] its type has an instance-implicit binder"
    verdict "(M8) a tactic configuration, which Lean evaluates as a program: the scan names it" "$LOG" \
      "$S/Oracle.lean:6:12: [syntax] syntax of kind \`Lean.Parser.Tactic.valConfigItem\` is not on the allow-list"
    verdict "a theorem with a universe parameter: the scan and the audit name it" "$LOG" \
      "$S/Universe.lean:3:9: [universe] the declaration name carries universe parameters" \
      "$LIBRARY.Selftest.anySort: [universes] it has the universe parameters [u]"
    verdict "a simp attribute: the scan names the attribute, the audit names the lemma" "$LOG" \
      "$S/Simp.lean:3:1: [syntax] syntax of kind \`Lean.Parser.Term.attributes\` is not on the allow-list" \
      "$LIBRARY.Selftest.addZero: [simp] registered in the simp set \`simp\` in $LIBRARY.Selftest.Simp"
    verdict "a definition of a metaprogramming type, written with allowed syntax only: the audit names it" "$LOG" \
      "$LIBRARY.Selftest.piece: [meta] its type mentions"
    verdict "a definition that hides a name of Mathlib inside the library's namespace, written with allowed syntax only: the audit names it" "$LOG" \
      "$LIBRARY.Selftest.Continuous: [shadowing] inside its namespace the name \`Continuous\` would mean it"
    verdict "an opaque, an unsafe and a partial definition (round 4, issue 9): the scan names the first keyword, the audit names each declaration" "$LOG" \
      "$S/Kinds.lean:3:1: [syntax] syntax of kind \`Lean.Parser.Command.opaque\` is not on the allow-list" \
      "$LIBRARY.Selftest.hidden: [kinds] declared as opaque" "$LIBRARY.Selftest.unsafeId: [kinds] unsafe" \
      "$LIBRARY.Selftest.loop: [kinds] declared as opaque" "$LIBRARY.Selftest.loop._unsafe_rec: [kinds] partial"
    verdict "definitions marked reducible (\`abbrev\`) and irreducible, and the two scoped instances, which Lean marks with the reducibility of instances (round 4, issue 9): the audit names each one" "$LOG" \
      "$LIBRARY.Selftest.Small: [reducible] marked Lean.ReducibilityStatus.reducible" \
      "$LIBRARY.Selftest.sealed: [reducible] marked Lean.ReducibilityStatus.irreducible" \
      "$LIBRARY.Selftest.Plain.fakeLE: [reducible] marked Lean.ReducibilityStatus.instanceReducible" \
      "$LIBRARY.Selftest.Behind.fakeLE: [reducible] marked Lean.ReducibilityStatus.instanceReducible"
    verdict "an argument with a default value, written with allowed syntax only (\`optParam\`; round 4, issue 9): the audit names the declaration" "$LOG" \
      "$LIBRARY.Selftest.withDefault: [binders] its type has an argument with a default value or a default tactic"
    verdict "a module that writes a file into scripts/ while it is compiled (round 4, issue 9): the scan names the command, and the digests taken at the end of the run name the new file" "$LOG" \
      "$S/Writer.lean:1:1: [command] a command of kind \`Lean.Parser.Command.eval\` is not on the allow-list" \
      "RESULT sources-unchanged: FAILED (a checked file changed while the check ran)" \
      "scripts/written-while-compiling.txt"
    verdict "(tree) file names that the source tree may not have (round 4, issue 9): a non-ASCII letter, a leading \`_\`, the extension .LEAN and a symbolic link: the scan names each one" "$LOG" \
      "$S/$NONASCII.lean: [tree] not a \`.lean\` file whose name begins with an ASCII letter and is made of ASCII letters, digits and \`_\`" \
      "$S/_Under.lean: [tree] not a \`.lean\` file whose name begins with an ASCII letter" \
      "$S/Upper.LEAN: [tree] not a \`.lean\` file whose name begins with an ASCII letter" \
      "$S/Link.lean: [tree] a symbolic link"
    if grep -q -E "^$S/(Meta|Shadow|Default)\.lean:" "$LOG"; then
      flunk "(src) the scan reported a module that was meant to show what only the audit sees (Meta, Shadow, Default); update these controls"
    fi
  fi
fi
fi

# ---------------------------------------------------------------------------
if want stored; then
echo "== (stored) a compiled file that was not made from the present sources =="
# A module whose compiled file is older than the module it imports: its stored axiom list
# (computed when it was compiled) no longer agrees with the declarations it refers to. The
# audit compares the axioms it finds by walking the declarations with the stored lists (round
# 4, issue 9). The copy is built by `lake build` and the audit is run by hand, as in (origin).
# (The theorem is not proved by `rfl`: Lean would add it to an environment extension that is
# not on the allow-list, and the audit would refuse that too.)
copy_project stored "$BASE"
add_module stored Provider no <<'EOF'
namespace VoltageToBit.Selftest

def provided : Nat := 0

end VoltageToBit.Selftest
EOF
add_module stored User yes <<'EOF'
import VoltageToBit.Selftest.Provider

namespace VoltageToBit.Selftest

theorem usesProvided : provided ≤ provided := Nat.le_refl provided

end VoltageToBit.Selftest
EOF
USER_OLEAN="$TMP/stored/.lake/build/lib/lean/$LIBRARY/Selftest/User.olean"
(cd "$TMP/stored" && lake build "$LIBRARY" --no-ansi) >"$TMP/stored-build1.log" 2>&1
s_first=$?
cp "$USER_OLEAN" "$TMP/User.olean.first" 2>/dev/null
# the module that is imported changes, so that its definition depends on an axiom (an allowed one)
cat >"$TMP/stored/$LIBRARY/Selftest/Provider.lean" <<'EOF'
namespace VoltageToBit.Selftest

noncomputable def provided : Nat := Classical.choice ⟨0⟩

end VoltageToBit.Selftest
EOF
(cd "$TMP/stored" && lake build "$LIBRARY" --no-ansi) >"$TMP/stored-build2.log" 2>&1
s_second=$?
if [ "$s_first" != 0 ] || [ "$s_second" != 0 ] || [ ! -f "$TMP/User.olean.first" ]; then
  flunk "(stored) the copy did not build (exit status $s_first, then $s_second); update this control"
  show_tail "$TMP/stored-build2.log"
else
  cp "$USER_OLEAN" "$TMP/User.olean.second"
  cp "$TMP/User.olean.first" "$USER_OLEAN"
  (cd "$TMP/stored" && lake env lean --run scripts/Audit.lean --root "$LIBRARY" --allow scripts/allowlist.txt) >"$TMP/stored.log" 2>&1
  s_status=$?
  if [ "$s_status" = 1 ] && absent "$TMP/stored.log" "AUDIT OK"; then
    verdict "(stored) the compiled file of a module, left from before the module it imports changed: the audit finds an axiom that the stored axiom list does not have, and refuses the declaration" "$TMP/stored.log" \
      "$LIBRARY.Selftest.usesProvided: [axioms] walking the declarations gives [Classical.choice], the list stored in the compiled file says [no axioms]" \
      "AUDIT FAILED: 1 refused"
  else
    flunk "(stored) the audit program exited with status $s_status, or it said AUDIT OK"
    show_tail "$TMP/stored.log"
  fi
  cp "$TMP/User.olean.second" "$USER_OLEAN"
  (cd "$TMP/stored" && lake env lean --run scripts/Audit.lean --root "$LIBRARY" --allow scripts/allowlist.txt) >"$TMP/stored.log" 2>&1
  s_status=$?
  kind positive
  if [ "$s_status" = 0 ] && present "$TMP/stored.log" "AUDIT OK"; then
    pass "(stored) with the compiled file made from the present sources the same command passes"
  else
    flunk "(stored) the audit program does not pass on the copy with its own compiled files (exit status $s_status), so the refusal above shows nothing"
    show_tail "$TMP/stored.log"
  fi
  kind negative
fi
fi

# ---------------------------------------------------------------------------
if want origin; then
echo "== (origin) compiled files of the library that come from another directory =="
# check.sh gives its tools no LEAN_PATH of the caller, so this cannot be staged through it: the
# audit program is run by hand, with a second copy of the compiled library in front of the
# search path.
copy_project origin "$BASE"
mkdir -p "$TMP/planted"
cp -R "$TMP/origin/.lake/build/lib/lean/." "$TMP/planted/"
# shellcheck disable=SC2016
(cd "$TMP/origin" && lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" exec lean --run scripts/Audit.lean --root "$2" --allow scripts/allowlist.txt' \
  sh "$TMP/planted" "$LIBRARY") >"$TMP/origin.log" 2>&1
o_status=$?
if [ "$o_status" = 1 ] && absent "$TMP/origin.log" "AUDIT OK"; then
  verdict "(origin) the audit refuses compiled files of the library that the search path takes from another directory than .lake/build of the project" "$TMP/origin.log" \
    "$LIBRARY: [origin] a module of the library, but its compiled file was not loaded from .lake/build/lib/lean of this project" \
    "AUDIT FAILED"
else
  flunk "(origin) the audit program exited with status $o_status, or it said AUDIT OK"
  show_tail "$TMP/origin.log"
fi
(cd "$TMP/origin" && lake env lean --run scripts/Audit.lean --root "$LIBRARY" --allow scripts/allowlist.txt) >"$TMP/origin.log" 2>&1
o_status=$?
kind positive
if [ "$o_status" = 0 ] && present "$TMP/origin.log" "AUDIT OK"; then
  pass "(origin) without the second copy the same command passes"
else
  flunk "(origin) the audit program does not pass on the copy itself (exit status $o_status), so the refusal above shows nothing"
  show_tail "$TMP/origin.log"
fi
kind negative
fi

# ---------------------------------------------------------------------------
if want m9; then
echo "== (m9) an error of lean in the audit program, after the audit has printed its result =="
copy_project m9 "$BASE"
sed 's/^  return if refused.isEmpty then 0 else 1$/  throw (IO.userError "selftest: thrown after the list of theorems")/' \
  scripts/Audit.lean >"$TMP/m9/scripts/Audit.lean"
if cmp -s scripts/Audit.lean "$TMP/m9/scripts/Audit.lean"; then
  flunk "(m9) scripts/Audit.lean does not end the way this control expects; update the control"
else
  run_check m9 --quick
  if [ "$CHECK_STATUS" = 1 ]; then
    verdict "(m9) the audit program fails after it has printed AUDIT OK and its list: check.sh fails at step axiom-audit and shows the error on the screen" "$LOG" \
      "AUDIT OK" "selftest: thrown after the list of theorems" "RESULT axiom-audit: FAILED" "CHECK FAILED: axiom-audit"
  else
    flunk "(m9) an error in the audit program: exit status $CHECK_STATUS"
    show_tail "$LOG"
  fi
fi
fi

# ---------------------------------------------------------------------------
if want bypass && [ "$BASE" != control ]; then
  flunk "(a) these controls need the positive control: name both in SELFTEST_ONLY"
elif want bypass; then
echo "== (a), (b) declaration added with the kernel check switched off (a full run of check.sh) =="
BAD=VoltageToBit.Selftest.bad
copy_project bypass control
add_module bypass KernelBypass yes <<'EOF'
import Lean

open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (.thmDecl {
  name := `VoltageToBit.Selftest.bad, levelParams := [], type := mkConst ``False,
  value := mkConst ``True.intro }))

theorem VoltageToBit.Selftest.oops : False := VoltageToBit.Selftest.bad
EOF
# (pyc) in the same copy, a module of the library in a directory named __pycache__, imported by
# the root (round 4, issue 1: such a module was compiled, scanned, audited and replayed, but its
# source was not digested). The scan does not read it, so step declaration-count fails too.
mkdir -p "$TMP/bypass/$LIBRARY/__pycache__"
cat >"$TMP/bypass/$LIBRARY/__pycache__/Extra.lean" <<'EOF'
namespace VoltageToBit.Selftest

theorem inCache : True := trivial

end VoltageToBit.Selftest
EOF
printf 'import %s.__pycache__.Extra\n' "$LIBRARY" >>"$TMP/bypass/$LIBRARY.lean"
run_check bypass --keep-going
if [ "$CHECK_STATUS" != 1 ]; then
  flunk "(a) kernel check switched off: check.sh exited with status $CHECK_STATUS, expected 1"
  show_tail "$LOG"
elif absent "$LOG" "RESULT build: ok" || absent "$LOG" "RESULT axiom-audit: ok" \
    || absent "$LOG" "RESULT import-closure: ok"; then
  flunk "(a) kernel check switched off: the control is not valid, because the build, the axiom audit or the import closure failed on the copy"
  grep -F "RESULT " "$LOG" | cut -c1-300 | sed 's/^/         /'
else
  echo "     the build and the axiom audit accept the file (RESULT build: ok, RESULT axiom-audit: ok): this is the gap of finding E1-08"
  if present "$CONTROL" "RESULT replay-modules: ok"; then
    verdict "(a) a declaration of False added with the kernel check switched off: leanchecker accepts the compiled files of the unmodified copy and rejects those of the copy with the declaration, naming it" \
      "$LOG" "leanchecker found a problem in VoltageToBit.Selftest.KernelBypass" "$BAD" \
      "(kernel) declaration type mismatch" "RESULT replay-modules: FAILED"
  else
    flunk "(a) leanchecker on the compiled files: it did not pass on the unmodified copy, so its failure here shows nothing"
  fi
  if [ ! -s "$TMP/export-tools.txt" ]; then
    echo "     note: no tool checked an export of the unmodified copy (see the notes above), so there is nothing to test for the export"
  elif absent "$LOG" "RESULT export: ok"; then
    flunk "(a) the export of the copy with the declaration was not written, so no tool was tested on it"
  fi
  while IFS= read -r tool; do
    [ -n "$tool" ] || continue
    if present "$CONTROL" "RESULT replay-export/$tool: NOT RUN"; then
      echo "     note: $tool is not installed; nothing to test"
      continue
    fi
    sed -n "/^-- $tool --\$/,/^RESULT replay-export\/$tool:/p" "$LOG" >"$TMP/tool.log"
    # how each tool says why it does not accept the declaration (observed with the toolchain of
    # DESCRIBED_FOR in check.sh); nanoda does not name the declaration
    case "$tool" in
      leanchecker|leanchecker-paranoid) reason="(kernel) declaration type mismatch, '$BAD' has type" ;;
      lean4lean) reason="at $BAD: (kernel) declaration type mismatch" ;;
      nanoda) reason="assertion failed: self.def_eq(u, v)" ;;
      con-leche) reason="con-leche: invalid: type mismatch in theorem $BAD" ;;
      con-ron) reason="con-ron: rejected: type mismatch in theorem [at theorem $BAD" ;;
      *) reason="$BAD" ;;
    esac
    if present "$CONTROL" "RESULT replay-export/$tool: ok" && present "$LOG" "RESULT replay-export/$tool: FAILED" \
        && present "$TMP/tool.log" "$reason"; then
      pass "(a) the same declaration, in the export: $tool accepts the export of the unmodified copy and does not accept the export of the copy with the declaration; it says: $reason"
    else
      flunk "(a) the same declaration, in the export: $tool (control: $(grep -F "RESULT replay-export/$tool:" "$CONTROL" | cut -c1-80); with the declaration: $(grep -F "RESULT replay-export/$tool:" "$LOG" | cut -c1-80); its reason \"$reason\" $(if present "$TMP/tool.log" "$reason"; then echo "was"; else echo "was not"; fi) shown)"
    fi
  done <"$TMP/export-tools.txt"
  verdict "(b) the source scan flags the file that switches the kernel check off: the import, the option and the command that runs code" "$LOG" \
    "VoltageToBit/Selftest/KernelBypass.lean:1:1: [import] import of \`Lean\`" \
    "VoltageToBit/Selftest/KernelBypass.lean:5:1: [syntax] syntax of kind \`Lean.Parser.Command.set_option\` is not on the allow-list" \
    "VoltageToBit/Selftest/KernelBypass.lean:6:1: [syntax] syntax of kind \`Lean.runCmd\` is not on the allow-list" \
    "RESULT source-scan: FAILED"
  verdict "(pyc) a module of the library in a directory named __pycache__, imported by $LIBRARY.lean (round 4, issue 1): the scan refuses the directory and the import" "$LOG" \
    "$LIBRARY/__pycache__: [tree] a directory whose name does not begin with an ASCII letter or is not made of ASCII letters, digits and \`_\`" \
    "$LIBRARY.lean: [closure] import of \`$LIBRARY.__pycache__.Extra\`: there is no source file that the tree rule accepts for it ($LIBRARY/__pycache__/Extra.lean)" \
    "[import] import of \`$LIBRARY.__pycache__.Extra\`: only modules of Mathlib and of $LIBRARY are allowed, with names whose components begin with an ASCII letter"
  if present "$TMP/bypass/evidence/lean/sources.sha256" "  $LIBRARY/__pycache__/Extra.lean" \
      && present "$TMP/bypass/evidence/lean/kernel-replay.txt" "    $LIBRARY.__pycache__.Extra"; then
    pass "(pyc) the record of that run lists the digest of the module's source file (sources.sha256) and the module among those that leanchecker replayed"
  else
    flunk "(pyc) the record of that run does not list the digest of $LIBRARY/__pycache__/Extra.lean, or not the module among those replayed"
  fi
  verdict "(s6) the record that this failed run wrote says so, with the steps" "$TMP/bypass/evidence/lean/kernel-replay.txt" \
    "outcome of the run of scripts/check.sh that wrote this record: FAILED: source-scan declaration-count replay-modules" \
    "RESULT replay-modules: FAILED"
fi
fi

# ---------------------------------------------------------------------------
if want g; then
echo "== (g) what the export checkers start from =="
TCBIN="$(lean --print-prefix)/bin"
if [ ! -x "$TCBIN/leanexport" ]; then
  echo "     note: leanexport is not installed; nothing to test"
else
  mkdir -p "$TMP/tiny/empty"
  # a small export from Lean core alone, and the same without the block that declares Eq
  lake env "$TCBIN/leanexport" Init -- Nat.succ_ne_zero >"$TMP/tiny/tiny.ndjson" 2>"$TMP/tiny/export.err"
  python3 -c 'import json, sys
src, dst = sys.argv[1], sys.argv[2]
names = {0: ()}
dropped = 0
with open(src, encoding="utf-8") as fin, open(dst, "w", encoding="utf-8") as fout:
    for line in fin:
        obj = json.loads(line)
        if "in" in obj:
            if "str" in obj:
                names[obj["in"]] = names[obj["str"]["pre"]] + (obj["str"]["str"],)
            else:
                names[obj["in"]] = names[obj["num"]["pre"]] + (obj["num"]["i"],)
        if "inductive" in obj and any(names[t["name"]] == ("Eq",) for t in obj["inductive"]["types"]):
            dropped += 1
            continue
        fout.write(line)
sys.exit(0 if dropped == 1 else 1)' "$TMP/tiny/tiny.ndjson" "$TMP/tiny/no-eq.ndjson"
  if [ $? != 0 ]; then
    flunk "(g) the small export has no single block that declares Eq; update this control"
  else
    cat >"$TMP/tiny/nanoda.json" <<EOF
{ "export_file_path": "$TMP/tiny/EXPORT", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true, "num_threads": 2, "pp_to_stdout": true,
  "print_success_message": true }
EOF
    tiny_run() {     # tiny_run <tool> <export>: exit status of the tool on the export
      case "$1" in
        nanoda_bin)
          sed "s|$TMP/tiny/EXPORT|$2|" "$TMP/tiny/nanoda.json" >"$TMP/tiny/nanoda-run.json"
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" "$TMP/tiny/nanoda-run.json") </dev/null >"$TMP/tiny/tool.log" 2>&1 ;;
        leanchecker|leanchecker-paranoid)
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" --from-export "$2") </dev/null >"$TMP/tiny/tool.log" 2>&1 ;;
        lean4lean)
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" --import "$2") </dev/null >"$TMP/tiny/tool.log" 2>&1 ;;
        *)
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" --jobs=2 "$2") </dev/null >"$TMP/tiny/tool.log" 2>&1 ;;
      esac
    }
    kind observation
    # tool | its line of acceptance | what it says when Eq is missing (observed with the toolchain
    # of DESCRIBED_FOR in check.sh; empty for the two that accept the export without Eq)
    while IFS='|' read -r tool accepts refuses; do
      [ -n "$tool" ] || continue
      if [ ! -x "$TCBIN/$tool" ]; then
        echo "     note: $tool is not installed; nothing to test"
        continue
      fi
      tiny_run "$tool" "$TMP/tiny/tiny.ndjson"; whole=$?
      cp "$TMP/tiny/tool.log" "$TMP/tiny/whole.log"
      tiny_run "$tool" "$TMP/tiny/no-eq.ndjson"; without=$?
      if [ -z "$refuses" ]; then
        if [ "$whole" = 0 ] && [ "$without" = 0 ] && present "$TMP/tiny/whole.log" "$accepts" && present "$TMP/tiny/tool.log" "$accepts"; then
          pass "(g) $tool accepts a small export, and also the same export without the declaration of Eq (\"$accepts\" both times): it does not start from an empty environment"
        else
          flunk "(g) $tool: exit status $whole on the small export and $without without Eq, or no line \"$accepts\"; check.sh says that it starts from a prelude of its own"
        fi
      elif [ "$whole" = 0 ] && [ "$without" != 0 ] && present "$TMP/tiny/whole.log" "$accepts" && present "$TMP/tiny/tool.log" "$refuses"; then
        pass "(g) $tool accepts a small export (\"$accepts\") and refuses the same export without the declaration of Eq: \"$refuses\""
      else
        flunk "(g) $tool: exit status $whole on the small export and $without without Eq, or not the messages \"$accepts\" and \"$refuses\"; check.sh says that it has no Eq built in"
        show_tail "$TMP/tiny/tool.log"
      fi
    done <<'EOF'
leanchecker|Lean default kernel accepts the solution|(kernel) unknown constant 'Eq'
leanchecker-paranoid|Lean default kernel accepts the solution|(kernel) unknown constant 'Eq'
lean4lean|checked |(kernel) unknown constant 'Eq'
nanoda_bin|Checked |declaration not found in infer_const, Eq
con-leche|con-leche: accepted |
con-ron|con-ron: accepted |
EOF
    kind negative
  fi
fi
fi

# ---------------------------------------------------------------------------
echo "== this checkout =="
kind checkout
if [ "$(tree_digest)" = "$BEFORE" ]; then
  pass "the library, the design files, the scripts and the evidence of this checkout are byte for byte what they were before the controls"
else
  flunk "a file of this checkout changed while the controls ran"
fi
COUNTS="PASS lines: $((N_NEGATIVE + N_POSITIVE + N_OBSERVATION + N_CHECKOUT)) (negative controls: $N_NEGATIVE, positive controls: $N_POSITIVE, observations: $N_OBSERVATION, check of this checkout: $N_CHECKOUT); FAIL lines: $N_FAIL"
if [ -n "${SELFTEST_ONLY:-}" ]; then
  echo "PARTIAL SELFTEST (SELFTEST_ONLY=$SELFTEST_ONLY): $(if [ "$STATUS" = 0 ]; then echo "no FAIL line"; else echo "see the FAIL lines above"; fi). $COUNTS. This is not a pass of the self-test."
elif [ "$STATUS" = 0 ]; then
  echo "SELFTEST PASSED: every defect was reported by the step that is meant to catch it. $COUNTS."
else
  echo "SELFTEST FAILED: see the FAIL lines above. $COUNTS."
fi
exit "$STATUS"
