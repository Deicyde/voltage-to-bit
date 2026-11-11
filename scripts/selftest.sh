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
# to take about five times as long as one full run of check.sh.
#
# First, a positive control: a copy without any build product must pass a full
# run, so that a failure below is due to the defect and not to the copying;
# and the records check.sh writes for that copy must be the ones in
# evidence/lean/ of this checkout, which shows that those records can be
# reproduced from the files alone, in another directory.
#
# Then the controls, with the finding of the review each one answers:
#   (cfg) the build configuration is not the pinned one: each of a list of
#       changes to lakefile.toml, lake-manifest.json and lean-toolchain, and a
#       lakefile.lean next to lakefile.toml, stops check.sh at step config,
#       before any Lean tool runs (B1, S5)
#   (b1) sources that do not compile cannot pass on compiled files left by an
#       earlier build, also when lakefile.toml names no default target or
#       another one and the pin is changed to accept that (B1)
#   (s5) with the autoImplicit lines deleted and the pin changed to accept
#       that, a statement with a misspelt name still does not pass: the scan
#       reads the options that the build passed to the compiler (S5)
#   (e) a design file that no longer matches the generated Lean file
#   (d) a failing build makes check.sh exit non-zero, at the build step
#   (src) one copy with several modules, each with one defect, and a full list
#       of what the scan and the audit must say about each: a file outside the
#       import closure (c); a declared axiom (f); a scoped instance in plain
#       sight (S3) and one behind `/-/-/` (B2); an indented `variable?` (S4);
#       a tactic configuration that carries a program (M8); a universe
#       parameter; a simp attribute; a notation; a definition of a
#       metaprogramming type; a definition that hides a name of Mathlib
#   (a) a declaration added with the kernel check switched off, as in
#       review/tooling/AuditGapDemo.lean, passes the build and the axiom audit
#       and is rejected by the replay steps: one line for leanchecker on the
#       compiled files, and one line for each tool that checks the export and
#       is installed. A line says PASS only if the same tool accepted the
#       unmodified copy.
#   (b) the source scan flags that file
#   (origin) the audit refuses compiled files of the library that are loaded
#       from another directory than .lake/build of the project
#   (m9) when lean fails in the audit program after the audit has printed its
#       result, check.sh shows the error (M9)
#   (s6) --quick says how the last full run on the present files ended (S6)
#   (g) what the export checkers start from: with the declaration of Eq
#       removed from a small export, four of them refuse it and con-leche and
#       con-ron accept it (M7)
#   and two sets of small cases for the source scan and for the design
#   generator (scripts/selftest_static.py).
#
# SELFTEST_KEEP=1 keeps the temporary directory and prints its path.
# SELFTEST_ONLY="<tags>" runs only the named groups of controls (static, control,
# s6, cfg, b1, s5, e, d, src, origin, m9, bypass, g), for work on this script; the copies are then
# made from the build products of this checkout when the positive control is not
# among them, and the last line says that the self-test was partial.
set -u

# an environment of its own, as scripts/check.sh gives itself
case "${1:-}" in
  --clean-environment) shift ;;
  *)
    exec env -i HOME="${HOME:-}" PATH="${PATH:-/usr/bin:/bin}" TMPDIR="${TMPDIR:-/tmp}" \
      LC_ALL=C PYTHONUTF8=1 PYTHONIOENCODING=utf-8 PYTHONDONTWRITEBYTECODE=1 \
      LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true LAKE_CONFIG=/nonexistent/lake-config.toml \
      CHECK_REPLAY_JOBS="${CHECK_REPLAY_JOBS:-1}" CHECK_SCAN_JOBS="${CHECK_SCAN_JOBS:-2}" \
      CHECK_BUILD_JOBS="${CHECK_BUILD_JOBS:-}" SELFTEST_KEEP="${SELFTEST_KEEP:-0}" \
      SELFTEST_ONLY="${SELFTEST_ONLY:-}" \
      sh "$0" --clean-environment "$@" ;;
esac
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
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
pass() { echo "PASS $1"; }
flunk() { echo "FAIL $1"; STATUS=1; }
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
  python3 -c 'import hashlib, pathlib
h = hashlib.sha256()
roots = ["VoltageToBit.lean", "VoltageToBit", "designs", "scripts", "evidence", "lakefile.toml",
         "lake-manifest.json", "lean-toolchain"]
files = []
for root in roots:
    path = pathlib.Path(root)
    files += [path] if path.is_file() else [p for p in path.rglob("*") if p.is_file()]
for path in sorted(files, key=lambda p: p.as_posix()):
    if "__pycache__" in path.parts:
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
python3 -B scripts/selftest_static.py "$ROOT" "$TMP/static" || STATUS=1
fi

# ---------------------------------------------------------------------------
: >"$TMP/export-tools.txt"
CONTROL="$TMP/control-full.log"
: >"$CONTROL"
if want control; then
echo "== positive control: a copy without build products (a full run of check.sh) =="
BASE=control
copy_project control none
run_check control
cp "$LOG" "$CONTROL"
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
grep '^RESULT replay-export/' "$CONTROL" | sed 's|^RESULT replay-export/||; s|:.*||' >"$TMP/export-tools.txt"
grep '^RESULT .*: NOT RUN' "$CONTROL" | sed 's/^/     note: /'
fi

# ---------------------------------------------------------------------------
if want s6 && [ "$BASE" != control ]; then
  flunk "(s6) these controls need the positive control: name both in SELFTEST_ONLY"
elif want s6; then
echo "== (s6) --quick says how the last full run on these files ended =="
run_check control --quick
if [ "$CHECK_STATUS" = 0 ]; then
  verdict "(s6) --quick after a full run that passed: it passes, compiles nothing again, and says that the record is for these same files and that the run passed" "$LOG" \
    "RESULT import-closure: ok" "0 compiled in this run, the others reused" \
    "is for these same files, and that run PASSED." "QUICK CHECK PASSED (steps 1 to 6)." \
    "no declaration was re-checked by any kernel in this run"
else
  flunk "(s6) --quick on the unmodified copy after its full run: exit status $CHECK_STATUS"
  show_tail "$LOG"
fi
# the same record, as a full run that failed at the kernel replay would have left it
sed 's/^  outcome of the run of scripts\/check.sh that wrote this record: every step that was run passed\.$/  outcome of the run of scripts\/check.sh that wrote this record: FAILED: replay-modules/' \
  "$TMP/control/evidence/lean/kernel-replay.txt" >"$TMP/failed-record.txt"
if cmp -s "$TMP/failed-record.txt" "$TMP/control/evidence/lean/kernel-replay.txt"; then
  flunk "(s6) the record has no outcome line of the expected form; update this control"
else
  cp "$TMP/failed-record.txt" "$TMP/control/evidence/lean/kernel-replay.txt"
  run_check control --quick
  if [ "$CHECK_STATUS" = 0 ] && absent "$LOG" "that run PASSED"; then
    verdict "(s6) --quick when the record of the last full run on these files says FAILED: the line that reports the quick check says so" "$LOG" \
      "is for these same files, and that run FAILED: replay-modules." \
      "QUICK CHECK PASSED (steps 1 to 6)."
    tail -n 1 "$LOG" | grep -q -F "that run FAILED: replay-modules." \
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
  # the unchanged configuration passes step 2's comparison; the copy has no dependencies
  (cd "$TMP/cfg" && PATH="$SAFE_PATH" sh scripts/check.sh --quick) >"$TMP/cfg.log" 2>&1
  c_status=$?
  if [ "$c_status" = 1 ] && present "$TMP/cfg.log" "pinned: lakefile.toml" && present "$TMP/cfg.log" "pinned: lake-manifest.json" \
      && present "$TMP/cfg.log" "pinned: lean-toolchain" && absent "$TMP/cfg.log" "NOT THE PINNED FILE" \
      && present "$TMP/cfg.log" "NOT READY: .lake/packages/mathlib is missing" \
      && present "$TMP/cfg.log" "CHECK FAILED: config" && absent "$TMP/cfg.log" "== 3."; then
    pass "(cfg) the unchanged configuration files are accepted as the pinned ones; in a copy without the dependencies check.sh then stops at step config and says that .lake/packages/mathlib is missing"
  else
    flunk "(cfg) the unchanged configuration files are not accepted, or a copy without dependencies did not stop at step config (exit status $c_status)"
    show_tail "$TMP/cfg.log"
  fi
  # name | file | what must be reported | python expression that maps the text `t` of the file to the changed text
  while IFS='|' read -r c_name c_file c_expect c_edit; do
    [ -n "$c_name" ] || continue
    if [ "$c_file" = lakefile.lean ]; then
      : >"$TMP/cfg/lakefile.lean"
    else
      cp "$c_file" "$TMP/cfg/$c_file"
      (cd "$TMP/cfg" && python3 -c 'import sys
name, edit = sys.argv[1], sys.argv[2]
t = open(name, encoding="utf-8", newline="").read()
new = eval(edit)
if new == t:
    sys.exit(3)
open(name, "w", encoding="utf-8", newline="").write(new)' "$c_file" "$c_edit")
      if [ $? != 0 ]; then
        flunk "(cfg) $c_name: the file does not have the text this control changes; update the control"
        cp "$c_file" "$TMP/cfg/$c_file"
        continue
      fi
    fi
    (cd "$TMP/cfg" && PATH="$SAFE_PATH" sh scripts/check.sh --quick --keep-going) >"$TMP/cfg.log" 2>&1
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
echo "== (s5) a build without autoImplicit = false, and names that are bound nowhere =="
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
  if [ "$CHECK_STATUS" = 1 ] && present "$LOG" "RESULT config: ok" && present "$LOG" "RESULT build: ok"; then
    verdict "(s5) lakefile.toml without the autoImplicit lines, the pin changed to accept it, and two statements with names that are bound nowhere: the build accepts them; the scan reports that the file was compiled without the options, and the audit names the theorem that got a universe parameter" "$LOG" \
      "$LIBRARY/Selftest/Auto.lean: [options] the build did not pass \`autoImplicit = false\` and \`relaxedAutoImplicit = false\`" \
      "RESULT source-scan: FAILED" \
      "$LIBRARY.Selftest.thresholds_agree: [universes] it has the universe parameters" \
      "RESULT axiom-audit: FAILED"
  else
    flunk "(s5) the control is not valid: exit status $CHECK_STATUS, or the configuration or the build of the copy was refused"
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
      "$LOG" "STALE:" "RESULT design-record: FAILED" "CHECK FAILED: design-record"
  else
    flunk "(e) stale design record: exit status $CHECK_STATUS, or check.sh went on after the failure"
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
  verdict "(d) a module that does not compile: check.sh stops with exit status 1 at step build" \
    "$LOG" "RESULT config: ok" "RESULT build: FAILED (lake build $LIBRARY exited with status" "CHECK FAILED: build"
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
  run_check src --quick --keep-going
  S="$LIBRARY/Selftest"
  if [ "$CHECK_STATUS" != 1 ] || absent "$LOG" "RESULT build: ok"; then
    flunk "(src) the controls are not valid: check.sh exited with status $CHECK_STATUS, or the copy with the defects did not build"
    show_tail "$LOG"
  else
    verdict "(src) the copy fails at the steps source-scan, axiom-audit, import-closure and declaration-count, and the build accepts all of it" "$LOG" \
      "RESULT build: ok" "RESULT source-scan: FAILED" "RESULT axiom-audit: FAILED" "RESULT import-closure: FAILED" \
      "RESULT declaration-count: FAILED" "CHECK FAILED: source-scan axiom-audit import-closure declaration-count"
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
    if grep -q -E "^$S/(Meta|Shadow)\.lean:" "$LOG"; then
      flunk "(src) the scan reported the last two modules, which were meant to show what only the audit sees; update these controls"
    fi
  fi
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
if [ "$o_status" = 0 ] && present "$TMP/origin.log" "AUDIT OK"; then
  pass "(origin) without the second copy the same command passes"
else
  flunk "(origin) the audit program does not pass on the copy itself (exit status $o_status), so the refusal above shows nothing"
  show_tail "$TMP/origin.log"
fi
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
    if grep -q -F -- "$BAD" "$TMP/tool.log"; then
      named="its output names the declaration"
    else
      # the first line that says why, without thread or process numbers
      named="its output does not name the declaration; it says: $(sed -n '3,$p' "$TMP/tool.log" \
        | grep -i -E 'assert|reject|invalid|mismatch|error' | head -n 1 | sed 's/^ *//' | cut -c1-100)"
    fi
    if present "$CONTROL" "RESULT replay-export/$tool: ok" && present "$LOG" "RESULT replay-export/$tool: FAILED"; then
      pass "(a) the same declaration, in the export: $tool accepts the export of the unmodified copy and does not accept the export of the copy with the declaration ($named)"
    else
      flunk "(a) the same declaration, in the export: $tool (control: $(grep -F "RESULT replay-export/$tool:" "$CONTROL" | cut -c1-80); with the declaration: $(grep -F "RESULT replay-export/$tool:" "$LOG" | cut -c1-80))"
    fi
  done <"$TMP/export-tools.txt"
  verdict "(b) the source scan flags the file that switches the kernel check off: the import, the option and the command that runs code" "$LOG" \
    "VoltageToBit/Selftest/KernelBypass.lean:1:1: [import] import of \`Lean\`" \
    "VoltageToBit/Selftest/KernelBypass.lean:5:1: [syntax] syntax of kind \`Lean.Parser.Command.set_option\` is not on the allow-list" \
    "VoltageToBit/Selftest/KernelBypass.lean:6:1: [syntax] syntax of kind \`Lean.runCmd\` is not on the allow-list" \
    "RESULT source-scan: FAILED"
  verdict "(s6) the record that this failed run wrote says so, with the step" "$TMP/bypass/evidence/lean/kernel-replay.txt" \
    "outcome of the run of scripts/check.sh that wrote this record: FAILED: source-scan replay-modules" \
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
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" "$TMP/tiny/nanoda-run.json") >"$TMP/tiny/tool.log" 2>&1 ;;
        leanchecker|leanchecker-paranoid)
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" --from-export "$2") >"$TMP/tiny/tool.log" 2>&1 ;;
        lean4lean)
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" --import "$2") >"$TMP/tiny/tool.log" 2>&1 ;;
        *)
          (cd "$TMP/tiny/empty" && env -i "$TCBIN/$1" --jobs=2 "$2") >"$TMP/tiny/tool.log" 2>&1 ;;
      esac
    }
    for tool in leanchecker leanchecker-paranoid lean4lean nanoda_bin con-leche con-ron; do
      if [ ! -x "$TCBIN/$tool" ]; then
        echo "     note: $tool is not installed; nothing to test"
        continue
      fi
      tiny_run "$tool" "$TMP/tiny/tiny.ndjson"; whole=$?
      tiny_run "$tool" "$TMP/tiny/no-eq.ndjson"; without=$?
      case "$tool" in
        con-leche|con-ron)
          if [ "$whole" = 0 ] && [ "$without" = 0 ]; then
            pass "(g) $tool accepts a small export, and also the same export without the declaration of Eq: it does not start from an empty environment"
          else
            flunk "(g) $tool: exit status $whole on the small export and $without without Eq; check.sh says that it starts from a prelude of its own"
          fi ;;
        *)
          if [ "$whole" = 0 ] && [ "$without" != 0 ]; then
            pass "(g) $tool accepts a small export and refuses the same export without the declaration of Eq"
          else
            flunk "(g) $tool: exit status $whole on the small export and $without without Eq; check.sh says that it starts from an empty environment"
          fi ;;
      esac
    done
  fi
fi
fi

# ---------------------------------------------------------------------------
echo "== this checkout =="
if [ "$(tree_digest)" = "$BEFORE" ]; then
  pass "the library, the design files, the scripts and the evidence of this checkout are byte for byte what they were before the controls"
else
  flunk "a file of this checkout changed while the controls ran"
fi
if [ -n "${SELFTEST_ONLY:-}" ]; then
  echo "PARTIAL SELFTEST (SELFTEST_ONLY=$SELFTEST_ONLY): $(if [ "$STATUS" = 0 ]; then echo "no FAIL line"; else echo "see the FAIL lines above"; fi). This is not a pass of the self-test."
elif [ "$STATUS" = 0 ]; then
  echo "SELFTEST PASSED: every defect was reported by the step that is meant to catch it."
else
  echo "SELFTEST FAILED: see the FAIL lines above."
fi
exit "$STATUS"
