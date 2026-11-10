#!/bin/sh
# Negative controls for scripts/check.sh: does it notice what it is there to
# notice?
#
#   scripts/selftest.sh
#
# Nothing in this checkout is modified. Every control works on a throwaway
# copy of the project in a temporary directory (sources, scripts, design
# files and this checkout's build products; the prebuilt dependencies in
# .lake/packages are linked, never copied or written to). The copy is given a
# defect and its own scripts/check.sh is run on it.
#
# One line is printed per control: PASS if check.sh reported the defect at the
# step that is meant to catch it, FAIL otherwise. Exit status 1 if any line is
# FAIL. The build of this checkout must be up to date (run scripts/check.sh
# first). check.sh is run with --quick for the defects that the first five
# steps catch and in full twice: on the unmodified copy and on the copy with a
# kernel bypass. The output has no dates or timings. Expect it to take several
# times as long as one full run of check.sh.
#
#   (a) a declaration added with the kernel check switched off, as in
#       review/tooling/AuditGapDemo.lean, passes the build and the axiom audit
#       and is rejected by the replay steps: one line for leanchecker on the
#       compiled files, and one line for each tool that checks the export and
#       is installed. A line says PASS only if the same tool accepted the
#       unmodified copy.
#   (b) the forbidden-construct scan flags that file
#   (c) a source file outside the import closure is detected
#   (d) a failing build makes check.sh exit non-zero, at the build step
#   (e) a design file that no longer matches the generated Lean file
#   (f) a declared axiom fails the axiom audit
#   and two sets of small cases for the source scan and for the design
#   generator (scripts/selftest_static.py).
#
# A positive control comes first: an unmodified copy must pass a full run, so
# that a failure below is due to the defect and not to the copying; and the
# records check.sh writes for that copy must be the ones in evidence/lean/ of
# this checkout, which shows that those records can be reproduced from the
# files.
#
# SELFTEST_KEEP=1 keeps the temporary directory and prints its path.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2

TMP="$(mktemp -d "${TMPDIR:-/tmp}/vtb-selftest.XXXXXX")" || exit 2
cleanup() {
  if [ "${SELFTEST_KEEP:-0}" = 1 ]; then echo "kept: $TMP"; else rm -rf "$TMP"; fi
}
trap cleanup EXIT
trap 'exit 130' INT TERM

STATUS=0
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

copy_project() {   # copy_project <name>: a throwaway copy in $TMP/<name>
  c_dir="$TMP/$1"
  mkdir -p "$c_dir/.lake"
  cp -R VoltageToBit VoltageToBit.lean scripts designs lakefile.toml lake-manifest.json lean-toolchain "$c_dir/"
  rm -rf "$c_dir/scripts/__pycache__"
  cp -R .lake/build "$c_dir/.lake/build"
  if [ -d .lake/config ]; then cp -R .lake/config "$c_dir/.lake/config"; fi
  ln -s "$PACKAGES" "$c_dir/.lake/packages"
}
add_module() {     # add_module <copy> <Name> <imported: yes|no>; the Lean text is read from standard input
  mkdir -p "$TMP/$1/VoltageToBit/Selftest"
  cat >"$TMP/$1/VoltageToBit/Selftest/$2.lean"
  if [ "$3" = yes ]; then
    printf 'import VoltageToBit.Selftest.%s\n' "$2" >>"$TMP/$1/VoltageToBit.lean"
  fi
}
run_check() {      # run_check <copy> <options>...: output in $TMP/<copy>.log, exit status in CHECK_STATUS
  r_copy="$1"; shift
  (cd "$TMP/$r_copy" && sh scripts/check.sh "$@") >"$TMP/$r_copy.log" 2>&1
  CHECK_STATUS=$?
  LOG="$TMP/$r_copy.log"
}

# ---------------------------------------------------------------------------
echo "== small cases for the source scan and for the design generator =="
python3 -B scripts/selftest_static.py "$ROOT" "$TMP/static" || STATUS=1

# ---------------------------------------------------------------------------
echo "== positive control: an unmodified copy (a full run of check.sh) =="
copy_project control
run_check control
CONTROL="$LOG"
if [ "$CHECK_STATUS" = 0 ]; then
  verdict "control: an unmodified copy of the project passes a full run of check.sh" "$CONTROL" \
    "RESULT design-record: ok" "RESULT source-scan: ok" "RESULT build: ok" \
    "RESULT axiom-audit: ok" "RESULT import-closure: ok" "RESULT replay-modules: ok" \
    "PASSED" "Kernel replay: (1) the compiled files of the"
else
  flunk "control: an unmodified copy of the project passes a full run of check.sh (exit status $CHECK_STATUS)"
  show_tail "$CONTROL"
fi
DIFFER=""
for record in audit.txt versions.txt sources.sha256 source-scan.txt kernel-replay.txt; do
  cmp -s "evidence/lean/$record" "$TMP/control/evidence/lean/$record" || DIFFER="$DIFFER $record"
done
if [ -z "$DIFFER" ]; then
  pass "control: the records that run wrote (audit.txt, versions.txt, sources.sha256, source-scan.txt, kernel-replay.txt) are byte for byte those in evidence/lean/ of this checkout"
else
  flunk "control: records in evidence/lean/ of this checkout are not what a full run of check.sh writes for an unmodified copy:$DIFFER (run scripts/check.sh, without --whole-env, to bring them up to date)"
fi
grep '^RESULT replay-export/' "$CONTROL" | sed 's|^RESULT replay-export/||; s|:.*||' >"$TMP/export-tools.txt"
grep '^RESULT .*: NOT RUN' "$CONTROL" | sed 's/^/     note: /'

# ---------------------------------------------------------------------------
echo "== (e) stale design record =="
copy_project stale
sed 's/"eps": "2"/"eps": "2.5"/' designs/illustrative-1v8.json >"$TMP/stale/designs/illustrative-1v8.json"
if cmp -s designs/illustrative-1v8.json "$TMP/stale/designs/illustrative-1v8.json"; then
  flunk "(e) stale design record: the design file could not be changed; update this control"
else
  run_check stale --quick
  if [ "$CHECK_STATUS" = 1 ] && absent "$LOG" "RESULT source-scan:"; then
    verdict "(e) a design file that differs from the generated Lean file: check.sh stops with exit status 1 at step design-record" \
      "$LOG" "STALE:" "RESULT design-record: FAILED" "CHECK FAILED: design-record"
  else
    flunk "(e) stale design record: exit status $CHECK_STATUS, or check.sh went on after the failure"
    show_tail "$LOG"
  fi
fi

# ---------------------------------------------------------------------------
echo "== (d) failing build =="
copy_project broken
add_module broken Broken yes <<'EOF'
theorem VoltageToBit.Selftest.broken : (1 : Nat) = 2 := rfl
EOF
run_check broken --quick
if [ "$CHECK_STATUS" = 1 ] && absent "$LOG" "RESULT axiom-audit:"; then
  verdict "(d) a module that does not compile: check.sh stops with exit status 1 at step build" \
    "$LOG" "RESULT source-scan: ok" "RESULT build: FAILED (lake build exited with status" "CHECK FAILED: build"
else
  flunk "(d) failing build: exit status $CHECK_STATUS, or check.sh went on after the failure"
  show_tail "$LOG"
fi

# ---------------------------------------------------------------------------
echo "== (c) source file outside the import closure =="
copy_project orphan
add_module orphan Orphan no <<'EOF'
theorem VoltageToBit.Selftest.orphan : True := trivial
EOF
run_check orphan --quick
if [ "$CHECK_STATUS" = 1 ]; then
  verdict "(c) a source file that VoltageToBit.lean does not import: check.sh exits with status 1 at step import-closure and names the file" \
    "$LOG" "RESULT source-scan: ok" "RESULT build: ok" "RESULT axiom-audit: ok" \
    "SOURCE FILE NOT IMPORTED BY VoltageToBit.lean (not built, not audited): VoltageToBit.Selftest.Orphan" \
    "RESULT import-closure: FAILED" "CHECK FAILED: import-closure"
else
  flunk "(c) source file outside the import closure: exit status $CHECK_STATUS"
  show_tail "$LOG"
fi

# ---------------------------------------------------------------------------
echo "== (f) declared axiom =="
copy_project axiom
add_module axiom ExtraAxiom yes <<'EOF'
namespace VoltageToBit.Selftest

axiom selftestAxiom : False

theorem usesIt : (0 : Nat) = 1 := selftestAxiom.elim

end VoltageToBit.Selftest
EOF
run_check axiom --quick --keep-going
if [ "$CHECK_STATUS" = 1 ]; then
  verdict "(f) an axiom declared and used in the library: the axiom audit fails and names it (the build accepts it)" \
    "$LOG" "RESULT build: ok" "AUDIT FAILED" "VoltageToBit.Selftest.selftestAxiom" \
    "RESULT axiom-audit: FAILED" "RESULT import-closure: ok"
  verdict "(f) the source scan flags the same file" "$LOG" \
    "VoltageToBit/Selftest/ExtraAxiom.lean:3:1: [forbidden] \`axiom\`" "RESULT source-scan: FAILED"
else
  flunk "(f) declared axiom: exit status $CHECK_STATUS"
  show_tail "$LOG"
fi

# ---------------------------------------------------------------------------
echo "== (a), (b) declaration added with the kernel check switched off (a full run of check.sh) =="
BAD=VoltageToBit.Selftest.bad
copy_project bypass
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
  verdict "(b) the source scan flags the file that switches the kernel check off" "$LOG" \
    "VoltageToBit/Selftest/KernelBypass.lean:5:1: [forbidden] \`set_option\`" \
    "VoltageToBit/Selftest/KernelBypass.lean:6:1: [forbidden] \`run_cmd\`" \
    "RESULT source-scan: FAILED"
fi

# ---------------------------------------------------------------------------
echo "== this checkout =="
if [ "$(tree_digest)" = "$BEFORE" ]; then
  pass "the library, the design files, the scripts and the evidence of this checkout are byte for byte what they were before the controls"
else
  flunk "a file of this checkout changed while the controls ran"
fi
if [ "$STATUS" = 0 ]; then
  echo "SELFTEST PASSED: every defect was reported by the step that is meant to catch it."
else
  echo "SELFTEST FAILED: see the FAIL lines above."
fi
exit "$STATUS"
