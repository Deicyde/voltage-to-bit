#!/bin/sh
# Reproduce every formal check of this repository.
#
#   scripts/check.sh               steps 1 to 9 (a full run)
#   scripts/check.sh --whole-env   steps 1 to 10 (a full run with step 10)
#   scripts/check.sh --quick       steps 1 to 6: nothing is re-checked by a
#                                  kernel, compiled files are reused, no
#                                  record is written
#   --fresh        with --quick: recompile the library first, as a full run
#                  does (a full run always does; there it changes nothing)
#   --keep-going   do not stop at the first failing step: run every later step
#                  whose inputs exist and report each one (a failure of step 2
#                  always stops the run)
#
# A full run deletes this project's own build products (.lake/build and
# .lake/config) and compiles the library again; do not start one while
# something else uses them. The script does not write to .lake/packages, the
# prebuilt Mathlib. `lake build` compiles a module there only if the library
# imports a module of a dependency that is not compiled yet; step 3 then
# names it.
#
# Steps. Each prints "RESULT <step>: ok" or "RESULT <step>: FAILED"; a tool
# that is not installed prints "RESULT <step>: NOT RUN" (see Tools).
#   1 design-record    every generated Lean design record is what its JSON file
#                      generates, and every JSON file in designs/ has one
#   2 config           lakefile.toml, lake-manifest.json and lean-toolchain are,
#                      byte for byte, the files pinned in
#                      scripts/pinned-config.sha256; there is no lakefile.lean;
#                      the `lean` that runs reports the version that
#                      lean-toolchain names. A failure here always ends the run
#   3 build            `lake build VoltageToBit` (the library, by name) exits
#                      with status 0. In a full run every module of the library
#                      is compiled in this step (step 6 checks that Lake
#                      reported each one as built)
#   4 source-scan      Lean's own parser reads every source file of the library
#                      (scripts/SourceScan.lean; no text is lexed by a script).
#                      Every command and every syntax node is of a kind on the
#                      allow-list scripts/allowlist.txt, which holds the kinds
#                      the library uses; every file is in the import closure of
#                      VoltageToBit.lean. The head of scripts/SourceScan.lean
#                      lists the rules
#   5 axiom-audit      over every declaration stored in the compiled files of
#                      the library, not over a list of names
#                      (scripts/Audit.lean): none depends on an axiom other than
#                      propext, Classical.choice, Quot.sound; the library
#                      declares no axiom, opaque or unsafe constant; it has no
#                      instance and no simp lemma, scoped ones included, besides
#                      those Lean generates for every structure, and no entry in
#                      an environment extension outside the allow-list; no
#                      declaration written in a source file has an
#                      instance-implicit binder or a universe parameter. The
#                      head of scripts/Audit.lean lists the rules
#   6 import-closure   the .lean files of the library, the modules of the
#                      library in the audited environment and, in a full run,
#                      the modules that step 3 compiled are the same set
#     declaration-count  the number of declarations written in the source
#                      files, as step 4 counts them, is the number of
#                      declarations with a source position in the compiled
#                      files, as step 5 counts them
#   7 replay-modules   `leanchecker` sends the declarations stored in the
#                      compiled file of every module of the library (the
#                      compiler auxiliaries named in the audit excepted) to
#                      Lean's kernel again, on top of that module's imports as
#                      they are compiled (Mathlib is loaded, not re-checked)
#   8 export           `leanexport` writes every declaration of the library,
#                      and every declaration those depend on, directly or not
#                      (the part of Mathlib, of its dependencies and of Lean
#                      core that the library uses, proofs included), to one
#                      file; scripts/export_census.py confirms that every
#                      declaration of the library is in it and that it declares
#                      no axiom besides the three
#   9 replay-export    that file is checked by each of the six checkers listed
#                      under Tools. Four of them start from an empty
#                      environment; con-leche and con-ron start from a prelude
#                      that is built into them
#  10 whole-env        (--whole-env only) `leanchecker --fresh` sends every
#                      declaration of every module that the library imports,
#                      directly or not, to Lean's kernel, from an empty
#                      environment, whether the library uses the declaration
#                      or not. That is the part of Mathlib that the library
#                      imports, its dependencies and Lean core; modules of
#                      Mathlib that the library does not import are not
#                      compiled here and are never looked at
#   at the end, sources-unchanged: the checked files have the digests they had
#                      before step 1 (reported only when it fails)
#
# Tools. The script starts itself again with an environment of its own: HOME,
# PATH, TMPDIR and the CHECK_* variables below are passed on, a few variables
# are set by the script, and nothing else is, so LEAN_PATH, ELAN_TOOLCHAIN,
# LAKE_* and the like have no effect. `lean` is found once through PATH in the
# project directory; every Lean tool is then run from the bin directory of
# that toolchain (`lean --print-prefix`) and from nowhere else. Step 2 fails
# unless that `lean` reports the version that lean-toolchain names, and the
# record identifies the programs of the toolchain by a digest. python3, git
# and the standard utilities come from PATH and are trusted, and so is the
# toolchain that PATH leads to. `lake help check` of the toolchain names the
# checkers it bundles; the record quotes the sentence. A tool that is not in the bin
# directory is reported as NOT RUN, by name, in the output, in the record and
# in the last line, and is not counted; the last line then begins differently
# (see Exit status). Only leanchecker is required: without it steps 7 and 10
# fail.
#   leanchecker           Lean's own kernel (steps 7, 9 and 10). Its source is
#                         in the toolchain: src/lean/LeanChecker.lean.
#   leanchecker-paranoid  Lean's own kernel again, in an executable of its
#                         own with the same options and messages; not counted
#                         as an independent implementation (step 9).
#   lean4lean, nanoda_bin, con-leche, con-ron
#                         four programs that are not Lean's kernel, according
#                         to `lake help check`, to the toolchain's LICENSES
#                         file and, where a tool has one, to its --help
#                         (step 9). Their sources are not in the toolchain
#                         and were not read; the record says of each what is
#                         known and where from. con-ron's --help calls it
#                         con-leche's checker in Rust, so these two are not
#                         independent designs. Where a tool reports how many
#                         declarations it checked, the number must be the one
#                         that scripts/export_census.py finds in the export.
#   leanexport            writes the export (step 8); it checks nothing.
# These descriptions were written for the toolchain named in DESCRIBED_FOR
# below; with another one the script says so and they have to be re-read.
#
# What a pass establishes. The last line of output says which parts apply.
#   steps 1 to 6 of a full run: the three configuration files are the pinned
#     ones; every module of the library was compiled in this run, by the
#     toolchain named in the record, from the source files whose digests are
#     in the record
#     (evidence/lean/sources.sha256; the digests are taken before step 1 and
#     again at the end and must agree); every .lean file of the library is one
#     of these modules; no declaration in the compiled files depends on an
#     axiom beyond the three of step 5; the sources consist of the kinds of
#     command and syntax on the allow-list; the design records match their
#     JSON files. Nothing has been re-checked by a kernel yet: a declaration
#     that was added with the kernel check switched off passes steps 3 and 5
#     (scripts/selftest.sh demonstrates it).
#   steps 1 to 6 with --quick: the same, except that a module is compiled only
#     when Lake finds its compiled file out of date. Lake decides that by
#     comparing a 64-bit hash of the present source file, and of what it
#     depends on, with the hash it stored in .lake/build when it compiled the
#     file. So the compiled files are those of the present sources as far as
#     that comparison goes, and only if nothing but Lake has written to
#     .lake/build; --fresh removes both conditions.
#   step 7: every declaration in the compiled files of the library (the
#     compiler auxiliaries named in the audit excepted) is accepted by Lean's
#     kernel on top of the compiled Mathlib.
#   steps 8 and 9: the declarations of the library, together with every
#     declaration of Mathlib, its dependencies and Lean core that they depend
#     on, are accepted by each checker that the last line names: from an empty
#     environment by leanchecker, leanchecker-paranoid, lean4lean and nanoda;
#     on top of their built-in prelude by con-leche and con-ron.
#   step 10: every declaration of every module that the library imports is
#     accepted by Lean's kernel from an empty environment.
# What it does not establish: that the statements mean what the prose says
# (read them, and the definitions they use), or that any physical device obeys
# the model. Nor
#   - anything when the library is hostile. Library code can run while the
#     library is compiled (in step 3, and wherever a compiled module is loaded
#     afterwards), with the rights of the user, before any checker starts; it
#     could alter the scripts, the tools or the files they read. Steps 4 and 5
#     refuse the constructs known to run code of the library when it is
#     compiled (`#eval`, `run_cmd`, `initialize`, macros, elaborators, tactic
#     configurations, and whatever else is not on the allow-list) and name the
#     file, but they run after the build. What the replay still catches when
#     the scripts and tools are intact: a declaration that Lean's kernel does
#     not accept, in the compiled files (step 7) or in the export (step 9);
#   - that Mathlib's compiled files in .lake/packages are the compilation of
#     the Mathlib revision in lake-manifest.json: they are used as they are
#     (Lake accepts them as up to date), and of their contents only the
#     declarations that the library depends on are re-checked, in step 9;
#   - that the export is faithful: the checkers of step 9 read what
#     `leanexport` wrote, not the compiled files (step 7 reads those, for the
#     library's own declarations);
#   - anything about declarations of Mathlib that the library does not depend
#     on, unless --whole-env is given (then those in imported modules are
#     re-checked, by Lean's own kernel only);
#   - that the four other checkers are sound, or independent of each other:
#     they are run as shipped;
#   - that step 4 or step 5 would notice every way of making a text mean
#     something else: they limit the constructs in use to the lists, and a
#     definition with a misleading name is not a construct.
#
# Records. A full run writes evidence/lean/: sources.sha256, versions.txt,
# source-scan.txt, audit.txt and kernel-replay.txt, all at the end, whether it
# passed or failed (kernel-replay.txt says which, and a record of a step that
# was not reached says so). They contain no dates or timings, so a full run
# with the same options on the same files with the same tools reproduces them
# byte for byte. --quick writes no record; it says whether the last record is
# for the present files and how that run ended.
#
# Each step prints the seconds it took. Step 3 takes time in proportion to the
# library, step 4 to the number of files (each is parsed in a process of its
# own that loads its imports), step 7 to the number of modules, steps 8 and 9
# to the size of what the library depends on, step 10 to the size of the whole
# imported environment.
#
# Environment:
#   CHECK_REPLAY_JOBS (default 1)  modules that `leanchecker` replays at a time
#     in step 7. Every job beyond the first was measured to need several GB of
#     memory of its own, and on a machine short of memory two jobs were no
#     faster than one.
#   CHECK_SCAN_JOBS (default 2)    files that step 4 parses at a time. Each job
#     loads the imports of one file and was measured to need about 2 GB.
#   CHECK_BUILD_JOBS (default: all cores)  threads that `lake build` uses.
#
# Exit status: 0 every step that was run passed; 1 a step failed; 2 usage.
# The last line of output says which happened. On success it begins with
# "ALL FORMAL CHECKS PASSED." if every tool was installed, with "THE FORMAL
# CHECKS THAT WERE RUN PASSED; NOT EVERY TOOL IS INSTALLED." otherwise, with
# "QUICK CHECK PASSED" for --quick, and goes on to say exactly what was
# compiled, what was replayed and by which tools, or that nothing was.
#
# Negative controls for this script: scripts/selftest.sh.
set -u

# An environment of our own: nothing but these variables reaches the tools.
if [ "${VTB_CHECK_ENV:-}" != clean ]; then
  exec env -i VTB_CHECK_ENV=clean HOME="${HOME:-}" PATH="${PATH:-/usr/bin:/bin}" TMPDIR="${TMPDIR:-/tmp}" \
    LC_ALL=C PYTHONUTF8=1 PYTHONIOENCODING=utf-8 PYTHONDONTWRITEBYTECODE=1 \
    LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true LAKE_CONFIG=/nonexistent/lake-config.toml \
    LEAN_ABORT_ON_PANIC=1 \
    CHECK_REPLAY_JOBS="${CHECK_REPLAY_JOBS:-1}" CHECK_SCAN_JOBS="${CHECK_SCAN_JOBS:-2}" \
    CHECK_BUILD_JOBS="${CHECK_BUILD_JOBS:-}" \
    sh "$0" "$@"
fi
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
whole_number() {   # whole_number <name> <value>: 1 or more
  case "$2" in
    ''|0*|*[!0-9]*)
      echo "check.sh: $1 must be a whole number, 1 or more; got '$2'" >&2; exit 2 ;;
  esac
}
JOBS="$CHECK_REPLAY_JOBS"; whole_number CHECK_REPLAY_JOBS "$JOBS"
SCAN_JOBS="$CHECK_SCAN_JOBS"; whole_number CHECK_SCAN_JOBS "$SCAN_JOBS"
BUILD_JOBS="$CHECK_BUILD_JOBS"
if [ -n "$BUILD_JOBS" ]; then whole_number CHECK_BUILD_JOBS "$BUILD_JOBS"; fi
# a full run always recompiles; --quick does only with --fresh
if [ "$QUICK" = 0 ] || [ "$FRESH" = 1 ]; then REBUILD=1; else REBUILD=0; fi

LIBRARY=VoltageToBit                       # the library and its root module
DESCRIBED_FOR="leanprover/lean4:v4.35.0"   # the toolchain whose tools are described here
EVIDENCE=evidence/lean
RECORDS="sources.sha256 versions.txt source-scan.txt audit.txt kernel-replay.txt"
STANDARD_AXIOMS='"propext", "Classical.choice", "Quot.sound"'

TMP="$(mktemp -d "${TMPDIR:-/tmp}/vtb-check.XXXXXX")" || exit 2
trap 'rm -rf "$TMP"' EXIT
trap 'exit 130' INT TERM
mkdir -p "$TMP/lists" "$TMP/empty" "$TMP/records" "$TMP/scan/lib"

T0="$(date +%s)"
FAILED=""            # steps that failed
NOTRUN=""            # tools that are not installed, by name
REPLAYED=""          # what the last line reports about the kernel replay
COMPILED=""          # what the last line reports about the build
LEAN=lean; TCBIN=""     # set in step 2

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
# The files that are checked, with their digests: the build configuration, the library
# sources (everything under the library's directory), the design files, the checking scripts.
list_sources() {
  python3 -c 'import hashlib, os, sys
library = sys.argv[1]
files = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", library + ".lean"]
def walk(top):
    found = []
    for root, dirs, names in os.walk(top):
        dirs[:] = sorted(d for d in dirs if d != "__pycache__")
        found += [os.path.join(root, n) for n in names if n != ".DS_Store"]
    return sorted(found)
files += walk(library)
files += sorted(os.path.join("designs", n) for n in os.listdir("designs") if n.endswith(".json"))
files += walk("scripts")
for f in files:
    with open(f, "rb") as handle:
        print(hashlib.sha256(handle.read()).hexdigest() + "  " + f)' "$LIBRARY"
}
# No local path in a record: the project directory, the home directory and the temporary
# directory are replaced by placeholders (they occur only in messages of failing tools).
sanitize() {
  python3 -c 'import os, sys
text = sys.stdin.buffer.read().decode("utf-8", "replace")
pairs = [(sys.argv[1], "<tmp>"), (os.path.realpath(sys.argv[1]), "<tmp>"),
         (os.getcwd(), "<project>"), (os.path.realpath(os.getcwd()), "<project>"),
         (os.path.realpath(os.path.join(".lake", "packages")), "<packages>"),
         (sys.argv[2], "<home>")]
for path, name in pairs:
    if len(path) > 1:
        text = text.replace(path, name)
sys.stdout.buffer.write(text.encode("utf-8"))' "$TMP" "$HOME"
}

# Records are put together in $TMP/records and installed at the end of a full run.
write_records() {
  rec_note="not written: the run of scripts/check.sh that wrote the records of this directory did not reach this step (see kernel-replay.txt)."
  for rec in $RECORDS; do
    [ -f "$TMP/records/$rec" ] || echo "$rec_note" >"$TMP/records/$rec"
  done
  {
    echo
    echo "Summary"
    echo "  results of the steps, in the order in which they were run:"
    indent <"$TMP/results.txt"
    echo "  tools not run because they are not installed: ${NOTRUN:-none}"
    if [ -n "$FAILED" ]; then
      echo "  outcome of the run of scripts/check.sh that wrote this record: FAILED:$FAILED"
    else
      echo "  outcome of the run of scripts/check.sh that wrote this record: every step that was run passed."
      echo "  compiled: $COMPILED"
      echo "  kernel replay: $REPLAYED"
    fi
  } >>"$TMP/records/kernel-replay.txt"
  mkdir -p "$EVIDENCE"
  for rec in $RECORDS; do
    sanitize <"$TMP/records/$rec" >"$EVIDENCE/$rec"
  done
  echo "records written to $EVIDENCE/: $RECORDS"
}
last_line() {
  # the files must be what they were when the run began
  if [ -f "$TMP/sources.begin" ]; then
    list_sources >"$TMP/sources.end" 2>&1
    if ! cmp -s "$TMP/sources.begin" "$TMP/sources.end"; then
      diff "$TMP/sources.begin" "$TMP/sources.end" | cut -c1-200 | head -n 10
      result "sources-unchanged: FAILED (a checked file changed while the check ran)"
      FAILED="$FAILED sources-unchanged"
    fi
  fi
  if [ "$QUICK" = 0 ]; then write_records; fi
  echo "elapsed: $(since "$T0")"
  if [ -n "$FAILED" ]; then
    echo "CHECK FAILED:$FAILED"
    exit 1
  fi
  if [ "$QUICK" = 1 ]; then
    echo "QUICK CHECK PASSED (steps 1 to 6). Compiled: $COMPILED THE KERNEL REPLAY WAS SKIPPED (--quick): no declaration was re-checked by any kernel in this run. $EARLIER"
  elif [ -z "$NOTRUN" ]; then
    echo "ALL FORMAL CHECKS PASSED. Compiled: $COMPILED Kernel replay: $REPLAYED"
  else
    echo "THE FORMAL CHECKS THAT WERE RUN PASSED; NOT EVERY TOOL IS INSTALLED. Compiled: $COMPILED Kernel replay: $REPLAYED"
  fi
  exit 0
}
# every result line is printed and kept for the record
result() { echo "RESULT $1" | tee -a "$TMP/results.txt"; }
ok() { result "$1: ok${2:+ ($2)}"; }
# stop <step> <reason>: a failure that ends the run even with --keep-going
stop() {
  result "$1: FAILED ($2)"
  FAILED="$FAILED $1"
  last_line
}
fail() {
  result "$1: FAILED ($2)"
  FAILED="$FAILED $1"
  if [ "$KEEP" = 0 ]; then last_line; fi
}
# notrun <step> <tool>: the tool is not installed; it is named and not counted
notrun() {
  result "$1: NOT RUN ($2 is not in the bin directory of the toolchain; it is not counted)"
  NOTRUN="$NOTRUN${NOTRUN:+, }$2"
}
# failed <step>: has this step, or a step whose name starts with it, failed?
failed() { case " $FAILED " in *" $1"*) return 0 ;; *) return 1 ;; esac; }

# What the last full run recorded, for --quick.
EARLIER="There is no record of a full run in $EVIDENCE/."

# The digests of the checked files, before anything is run.
: >"$TMP/results.txt"
RECORD="$TMP/records/kernel-replay.txt"
{
  echo "Record of a full run of scripts/check.sh. Written by that script; do not edit."
  echo "It has no dates or timings: a full run with the same options on the same files with the"
  echo "same tools reproduces it, and the four other records of this directory, byte for byte."
} >"$RECORD"
if ! list_sources >"$TMP/sources.begin" 2>"$TMP/sources.err"; then
  cut -c1-300 "$TMP/sources.err" | tail -n 3
  rm -f "$TMP/sources.begin"
  stop config "a file that the check needs is missing or cannot be read"
fi
cp "$TMP/sources.begin" "$TMP/records/sources.sha256"
SOURCES_DIGEST="$(sha256_of "$TMP/sources.begin")"
{
  echo
  echo "What was checked"
  echo "  files:     the build configuration, library sources, design files and checking scripts"
  echo "             listed in $EVIDENCE/sources.sha256 (sha256 of the list: $SOURCES_DIGEST)"
} >>"$RECORD"

# ---------------------------------------------------------------------------
echo "== 1. design records in sync with their JSON files =="
if python3 scripts/gen_design.py --check-all designs "$LIBRARY"; then
  ok design-record
else
  fail design-record "a generated design record is stale, a JSON design file was rejected or has no generated record; see the message above"
fi

# ---------------------------------------------------------------------------
echo "== 2. build configuration: the pinned files and the pinned toolchain =="
python3 -c 'import hashlib, json, os, sys
pin_file = sys.argv[1]
expected = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]
status = 0
pins = {}
for line in open(pin_file, encoding="utf-8").read().split("\n"):
    if not line.strip() or line.startswith("#"):
        continue
    digest, _, name = line.partition("  ")
    pins[name] = digest
if sorted(pins) != sorted(expected):
    print(f"NOT PINNED: {pin_file} must name exactly {expected}; it names {sorted(pins)}")
    status = 1
for name in expected:
    if os.path.islink(name) or not os.path.isfile(name):
        print(f"NOT THE PINNED FILE: {name} is missing or is not a regular file")
        status = 1
        continue
    digest = hashlib.sha256(open(name, "rb").read()).hexdigest()
    if digest != pins.get(name):
        print(f"NOT THE PINNED FILE: {name} has sha256 {digest}; {pin_file} pins {pins.get(name)}")
        status = 1
    else:
        print(f"pinned: {name} (sha256 {digest})")
for name in sorted(os.listdir(".")):
    if name.lower() == "lakefile.lean":
        print(f"NOT ALLOWED: {name}: Lake would use it in place of lakefile.toml, and it is a program")
        status = 1
if status == 0:
    # as read from the files
    print("lean-toolchain: " + open("lean-toolchain", encoding="utf-8").read().strip())
    section = None
    wanted = []
    for line in open("lakefile.toml", encoding="utf-8").read().split("\n"):
        if line.startswith("["):
            section = line.strip()
        elif section == "[[require]]" and line.strip():
            wanted.append(line.strip())
    print("lakefile.toml requires: " + ", ".join(wanted))
    for package in json.load(open("lake-manifest.json", encoding="utf-8"))["packages"]:
        how = "required by lakefile.toml" if not package.get("inherited") else "required by a dependency"
        url = package.get("url")
        rev = package.get("rev")
        name = package["name"]
        print(f"lake-manifest.json: {name} at {rev} from {url} ({how})")
sys.exit(status)' scripts/pinned-config.sha256 >"$TMP/config.txt" 2>&1
status=$?
cat "$TMP/config.txt"
MATHLIB_REV="$(sed -n 's/^lake-manifest.json: mathlib at \([0-9a-f]*\) .*/\1/p' "$TMP/config.txt")"
if [ "$status" != 0 ]; then
  # With another configuration `lake` may fetch or rebuild dependencies, or run a program.
  stop config "the build configuration is not the pinned one; nothing further is run, because with another configuration \`lake\` may download or rebuild dependencies. A deliberate change is made by editing scripts/pinned-config.sha256"
fi
PREFIX="$(lean --print-prefix 2>"$TMP/prefix.err")"
status=$?
TCBIN="$PREFIX/bin"
if [ "$status" != 0 ] || [ ! -x "$TCBIN/lean" ] || [ ! -x "$TCBIN/lake" ]; then
  cut -c1-300 "$TMP/prefix.err" | tail -n 3
  stop config "\`lean --print-prefix\` did not name a toolchain with lean and lake in its bin directory"
fi
LEAN="$TCBIN/lean"
# every `lake` command names the configuration file, so that no other file can stand in for it
lake_() { "$TCBIN/lake" --file=lakefile.toml "$@"; }
LEAN_VERSION="$("$LEAN" --version 2>&1)"
LAKE_VERSION="$("$TCBIN/lake" --version 2>&1)"
TOOLCHAIN="$(cat lean-toolchain)"
WANTED_VERSION="$(printf '%s\n' "$TOOLCHAIN" | sed -n '1s/^.*:v\{0,1\}//p')"
# which programs these are: one digest over the executables and shared libraries of the toolchain
TOOLCHAIN_FILES="$(python3 -c 'import hashlib, os, sys
prefix = sys.argv[1]
files = []
for sub, suffixes in (("bin", None), (os.path.join("lib", "lean"), (".dylib", ".so", ".dll"))):
    top = os.path.join(prefix, sub)
    for name in sorted(os.listdir(top)):
        path = os.path.join(top, name)
        if os.path.isfile(path) and (suffixes is None or name.endswith(suffixes)):
            files.append((sub + "/" + name, path))
total = hashlib.sha256()
for shown, path in files:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    total.update((h.hexdigest() + "  " + shown + "\n").encode())
print(f"{len(files)} files in bin and lib/lean of the toolchain (every file of bin, every shared library of lib/lean); sha256 of the list of their sha256 and names: {total.hexdigest()}")' "$PREFIX" 2>&1)"
{
  cat "$TMP/config.txt"
  echo "these three files are the ones pinned in scripts/pinned-config.sha256"
  echo "lean --version: $LEAN_VERSION"
  echo "lake --version: $LAKE_VERSION"
  echo "toolchain programs: $TOOLCHAIN_FILES"
} >"$TMP/records/versions.txt"
echo "lean --version: $LEAN_VERSION"
echo "lake --version: $LAKE_VERSION"
echo "toolchain programs: $TOOLCHAIN_FILES"
case "$LEAN_VERSION" in
  *"(version $WANTED_VERSION,"*) ok config "the three files are the pinned ones; the toolchain is $TOOLCHAIN" ;;
  *)
    stop config "lean-toolchain names $TOOLCHAIN, but the \`lean\` found through PATH in this directory reports: $LEAN_VERSION" ;;
esac
{
  echo "  config:    lakefile.toml, lake-manifest.json and lean-toolchain are the files pinned in"
  echo "             scripts/pinned-config.sha256"
  echo "  toolchain: $TOOLCHAIN (lean-toolchain); $LEAN_VERSION"
  echo "  mathlib:   $MATHLIB_REV (lake-manifest.json); used as compiled in .lake/packages, not"
  echo "             recompiled"
} >>"$RECORD"
TOOLCHAIN_NOTE=""
if [ "$TOOLCHAIN" != "$DESCRIBED_FOR" ]; then
  TOOLCHAIN_NOTE="NOTE: lean-toolchain says $TOOLCHAIN, but the descriptions of the tools in scripts/check.sh were written for $DESCRIBED_FOR; re-read them (--help of each tool) before relying on them."
  echo "$TOOLCHAIN_NOTE"
fi

# ---------------------------------------------------------------------------
echo "== 3. build: the library, by name =="
START="$(date +%s)"
if [ "$REBUILD" = 1 ]; then
  echo "removing this project's build products (.lake/build, .lake/config)"
  rm -rf .lake/build .lake/config
fi
if [ -n "$BUILD_JOBS" ]; then
  env LEAN_NUM_THREADS="$BUILD_JOBS" "$TCBIN/lake" --file=lakefile.toml build "$LIBRARY" --no-ansi >"$TMP/build.log" 2>&1
else
  lake_ build "$LIBRARY" --no-ansi >"$TMP/build.log" 2>&1
fi
status=$?
# the modules that Lake says it compiled in this run
sed -n 's/^.*\] Built \([^ ]*\) (.*$/\1/p' "$TMP/build.log" \
  | grep -E "^$LIBRARY(\\.|\$)" | LC_ALL=C sort -u >"$TMP/built-modules.txt"
N_BUILT="$(count_lines "$TMP/built-modules.txt")"
sed -n 's/^.*\] Built \([^ ]*\) (.*$/\1/p' "$TMP/build.log" \
  | grep -v -E "^$LIBRARY(\\.|\$)" | LC_ALL=C sort -u >"$TMP/built-elsewhere.txt"
if [ "$status" = 0 ]; then
  filter <"$TMP/build.log" | grep -v '\] Built \|\] Replayed ' | cut -c1-300 | tail -n 3
  echo "modules of the library compiled in this run: $N_BUILT; $(since "$START")"
  if [ -s "$TMP/built-elsewhere.txt" ]; then
    echo "NOTE: Lake also compiled $(count_lines "$TMP/built-elsewhere.txt") modules outside the library in this run, in .lake/packages (the library imports modules of a dependency that were not compiled yet):"
    head -n 20 "$TMP/built-elsewhere.txt" | indent
  fi
  ok build
else
  filter <"$TMP/build.log" | cut -c1-600 | tail -n 60
  fail build "lake build $LIBRARY exited with status $status"
fi

# ---------------------------------------------------------------------------
echo "== 4. source scan: every file read by Lean's parser, against the allow-list =="
if failed build; then
  echo "not run: the build failed"
  fail source-scan "not run: the build failed"
else
  START="$(date +%s)"
  # the scan program is compiled once, and then run for the library and for each file
  if lake_ env "$LEAN" --root=scripts -o "$TMP/scan/lib/SourceScan.olean" scripts/SourceScan.lean >"$TMP/scan-compile.log" 2>&1; then
    printf 'import SourceScan\n' >"$TMP/scan/main.lean"
    # shellcheck disable=SC2016
    lake_ env sh -c 'LEAN_PATH="$1:$LEAN_PATH" exec "$2" --run "$3" scan --self "$3" --allow "$4" --root "$5" --build .lake/build --jobs "$6"' \
      sh "$TMP/scan/lib" "$LEAN" "$TMP/scan/main.lean" scripts/allowlist.txt "$LIBRARY" "$SCAN_JOBS" >"$TMP/scan.txt" 2>"$TMP/scan.err"
    status=$?
  else
    cut -c1-600 "$TMP/scan-compile.log" | head -n 20
    : >"$TMP/scan.txt"; echo "scripts/SourceScan.lean does not compile" >"$TMP/scan.err"
    status=2
  fi
  cut -c1-1000 "$TMP/scan.txt"
  cut -c1-600 "$TMP/scan.err" | head -n 20
  cat "$TMP/scan.txt" "$TMP/scan.err" >"$TMP/records/source-scan.txt"
  echo "$(since "$START")"
  if [ "$status" = 0 ] && [ "$(tail -n 1 "$TMP/scan.txt")" = "no finding" ]; then
    ok source-scan
  elif [ "$status" = 1 ]; then
    fail source-scan "see the findings above"
  else
    fail source-scan "the scan did not complete (exit status $status)"
  fi
fi

# ---------------------------------------------------------------------------
echo "== 5. axiom audit over every declaration of the library =="
if failed build; then
  echo "not run: the build failed"
  fail axiom-audit "not run: the build failed"
else
  START="$(date +%s)"
  lake_ env "$LEAN" --run scripts/Audit.lean --root "$LIBRARY" --allow scripts/allowlist.txt --lists "$TMP/lists" >"$TMP/audit.log" 2>&1
  status=$?
  filter <"$TMP/audit.log" >"$TMP/records/audit.txt"
  sed '/^theorems with a name of their own/,$d' "$TMP/records/audit.txt" | cut -c1-2000
  echo "$(since "$START")"
  if [ "$status" = 0 ] && grep -q "^AUDIT OK" "$TMP/records/audit.txt"; then
    grep "^theorems with a name of their own" "$TMP/records/audit.txt" | sed "s|:\$| are listed in $EVIDENCE/audit.txt (a full run writes it)|"
    ok axiom-audit
  else
    # whatever the audit or `lean` said after the list of theorems began (an error of `lean` comes last)
    sed -n '/^theorems with a name of their own/,$p' "$TMP/records/audit.txt" \
      | grep -i -E 'error|exception|panic|AUDIT' | cut -c1-600 | head -n 20
    fail axiom-audit "the audit refused something, or lean exited with status $status; the reason is printed above"
  fi
fi

# ---------------------------------------------------------------------------
echo "== 6. source files, audited modules and compiled modules are the same set =="
if [ ! -f "$TMP/lists/modules.txt" ]; then
  echo "not run: the audit did not produce a list of modules"
  fail import-closure "not run: no list of modules"
else
  { [ -f "$LIBRARY.lean" ] && echo "$LIBRARY"
    find "$LIBRARY" -name '*.lean' | sed 's/\.lean$//; s#/#.#g'
  } | LC_ALL=C sort >"$TMP/source-modules.txt"
  LC_ALL=C sort "$TMP/lists/modules.txt" >"$TMP/env-modules.txt"
  n_src="$(count_lines "$TMP/source-modules.txt")"
  n_env="$(count_lines "$TMP/env-modules.txt")"
  echo "source files of the library ($LIBRARY.lean and $LIBRARY/**/*.lean): $n_src"
  echo "modules of the library in the audited environment: $n_env"
  closure=ok
  if ! cmp -s "$TMP/source-modules.txt" "$TMP/env-modules.txt"; then
    LC_ALL=C comm -23 "$TMP/source-modules.txt" "$TMP/env-modules.txt" \
      | sed "s/^/  SOURCE FILE NOT IMPORTED BY $LIBRARY.lean (not built, not audited): /"
    LC_ALL=C comm -13 "$TMP/source-modules.txt" "$TMP/env-modules.txt" \
      | sed 's/^/  MODULE IN THE ENVIRONMENT WITHOUT A SOURCE FILE: /'
    closure="$n_src source files but $n_env modules in the audited environment, or different names"
  elif [ "$REBUILD" = 1 ] && ! cmp -s "$TMP/built-modules.txt" "$TMP/env-modules.txt"; then
    LC_ALL=C comm -13 "$TMP/built-modules.txt" "$TMP/env-modules.txt" \
      | sed 's/^/  MODULE THAT LAKE DID NOT REPORT AS BUILT IN THIS RUN: /'
    LC_ALL=C comm -23 "$TMP/built-modules.txt" "$TMP/env-modules.txt" \
      | sed 's/^/  MODULE BUILT IN THIS RUN THAT IS NOT IN THE AUDITED ENVIRONMENT: /'
    closure="the build products were removed, but Lake reported $N_BUILT modules as built and the audited environment has $n_env"
  fi
  if [ "$closure" = ok ]; then
    if [ "$REBUILD" = 1 ]; then
      COMPILED="all $n_env modules of the library, in this run, after its build products had been removed (Lake reported each one as built)."
      ok import-closure "$n_src source files, $n_env modules in the audited environment, $N_BUILT modules compiled in this run, the same names"
    else
      COMPILED="$N_BUILT of the $n_env modules of the library in this run; the others were reused because Lake found them up to date (a comparison of 64-bit hashes kept in .lake/build; --fresh recompiles everything)."
      ok import-closure "$n_src source files, $n_env modules in the audited environment, the same names; $N_BUILT compiled in this run, the others reused"
    fi
  else
    fail import-closure "$closure"
  fi
  # declarations: what the parser saw in the text and what the compiled files hold
  n_scan="$(sed -n 's/^declarations written in the files: \([0-9][0-9]*\) .*/\1/p' "$TMP/scan.txt" 2>/dev/null)"
  n_audit="$(sed -n 's/^  written in a source file (Lean stored a source position): \([0-9][0-9]*\);.*/\1/p' "$TMP/records/audit.txt" 2>/dev/null)"
  echo "declarations written in the source files, as the scan counts them: ${n_scan:-none counted}"
  echo "declarations with a source position in the compiled files, as the audit counts them: ${n_audit:-none counted}"
  if [ -n "$n_scan" ] && [ "$n_scan" = "$n_audit" ]; then
    ok declaration-count "$n_scan"
  else
    fail declaration-count "the compiled files hold a declaration that the scan did not see as one in the text, or the reverse (or one of the two steps did not run)"
  fi
fi

# ---------------------------------------------------------------------------
# what was checked, and the tools
echo "== files and versions =="
echo "files: $(count_lines "$TMP/sources.begin") (build configuration, library sources, design files, checking scripts); sha256 of the list of their digests: $SOURCES_DIGEST"
echo "mathlib (lake-manifest.json): $MATHLIB_REV"

if [ "$QUICK" = 1 ]; then
  echo "== 7 to 9. kernel replay: SKIPPED (--quick) =="
  if [ -f "$EVIDENCE/kernel-replay.txt" ]; then
    outcome="$(sed -n 's/^  outcome of the run of scripts\/check.sh that wrote this record: //p' "$EVIDENCE/kernel-replay.txt" | tail -n 1)"
    case "$outcome" in
      "every step that was run passed.") outcome="that run PASSED" ;;
      FAILED*) outcome="that run $outcome" ;;
      *) outcome="the record does not say how that run ended" ;;
    esac
    if grep -q "sha256 of the list: $SOURCES_DIGEST" "$EVIDENCE/kernel-replay.txt"; then
      EARLIER="The record of the last full run ($EVIDENCE/kernel-replay.txt) is for these same files, and $outcome."
    else
      EARLIER="The record of the last full run ($EVIDENCE/kernel-replay.txt) is for DIFFERENT files ($outcome)."
    fi
  fi
  echo "$EARLIER"
  last_line
fi

# ---------------------------------------------------------------------------
# kernel replay. Everything below reads compiled files, so it needs the build.
N_MODULES="$(count_lines "$TMP/env-modules.txt" 2>/dev/null || echo 0)"
N_CHECKABLE="$(count_lines "$TMP/lists/constants.txt" 2>/dev/null || echo 0)"
N_SKIPPED="$(count_lines "$TMP/lists/skipped.txt" 2>/dev/null || echo 0)"
ENVIRONMENT="$(sed -n 's/^imported environment: //p' "$TMP/records/audit.txt" 2>/dev/null)"
BUNDLED="$(lake_ help check 2>/dev/null \
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
  echo "  compiled:  ${COMPILED:-the build or the comparison of the module lists failed; see the Summary}"
  echo "  library:   $N_MODULES modules; $N_CHECKABLE declarations that the replay steps re-check, and"
  echo "             $N_SKIPPED compiler auxiliaries that they leave out (named in $EVIDENCE/audit.txt)"
  echo "  imported environment, of which the library is a part: $ENVIRONMENT"
  echo
  echo "Where the tools come from"
  echo "  The script runs with an environment of its own (HOME, PATH, TMPDIR). \`lean\` is found"
  echo "  through PATH in the project directory; every Lean tool is then run from the bin directory"
  echo "  of that toolchain (\`lean --print-prefix\`) and from nowhere else. A tool that is not there"
  echo "  is reported as NOT RUN and is not counted."
  if [ -n "$BUNDLED" ]; then
    echo "  \`lake help check\` of this toolchain says about the checkers it bundles:"
    echo "    $BUNDLED"
  else
    echo "  \`lake help check\` of this toolchain does not name any bundled checker."
  fi
  if [ -n "$TOOLCHAIN_NOTE" ]; then echo "  $TOOLCHAIN_NOTE"; fi
} >>"$RECORD"

if failed build || failed axiom-audit || failed import-closure || [ ! -f "$TMP/lists/constants.txt" ]; then
  echo "== 7 to 9. kernel replay: not run, an earlier step that it depends on failed =="
  {
    echo
    echo "The kernel replay was not run: the build, the audit or the comparison of the module lists failed."
  } >>"$RECORD"
  fail replay-modules "not run: the build, the audit or the comparison of the module lists failed"
  last_line
fi

# --- step 7 ---------------------------------------------------------------
echo "== 7. leanchecker: compiled modules replayed against their imports ($JOBS at a time) =="
START="$(date +%s)"
{
  echo
  echo "1. Compiled modules replayed against the imported environment"
  echo "  tool:    $(tool_id leanchecker)"
  echo "  kind:    Lean's own kernel, the one that also checks declarations when a file is compiled"
  echo "  command: LEAN_NUM_THREADS=<jobs> lake env leanchecker -v $LIBRARY"
  echo "  does:    for every module whose name starts with $LIBRARY, sends each declaration"
  echo "           stored in the module's compiled file (the compiler auxiliaries excepted) to"
  echo "           Lean's kernel, on top of the environment formed by the module's imports. The"
  echo "           imports themselves (other modules of the library, Mathlib, Lean core) are"
  echo "           loaded as compiled; they are not re-checked by this step."
} >>"$RECORD"
if [ ! -x "$TCBIN/leanchecker" ]; then
  echo "  result:  not run, the tool is missing" >>"$RECORD"
  fail replay-modules "leanchecker is not in the bin directory of the toolchain, and this step needs it (--quick skips the replay)"
else
  env LEAN_NUM_THREADS="$JOBS" "$TCBIN/lake" --file=lakefile.toml env "$TCBIN/leanchecker" -v "$LIBRARY" >"$TMP/leanchecker.log" 2>&1
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
    {
      echo "  it said:"
      filter <"$TMP/leanchecker.log" | grep -v '^replaying ' | cut -c1-600 | head -n 12 | indent
      echo "  RESULT replay-modules: FAILED"
    } >>"$RECORD"
    fail replay-modules "leanchecker exited with status $status; its message is above (a declaration that the kernel rejects is named there)"
  elif ! cmp -s "$TMP/replayed-modules.txt" "$TMP/env-modules.txt"; then
    LC_ALL=C comm -3 "$TMP/replayed-modules.txt" "$TMP/env-modules.txt"
    echo "  RESULT replay-modules: FAILED" >>"$RECORD"
    fail replay-modules "the modules replayed are not the modules of the audited environment"
  else
    echo "  RESULT replay-modules: ok" >>"$RECORD"
    ok replay-modules "$n_rep modules"
    REPLAYED="(1) the compiled files of the $n_rep modules of the library, each on top of its imports as compiled, by leanchecker (Lean's own kernel)."
  fi
fi

# --- steps 8 and 9 --------------------------------------------------------
# check_export <step prefix> <export file> <hard error on unexpected axiom: true|false>
# Runs the checkers on an export and appends to the record. Sets ACCEPTED_KERNEL (Lean's own
# kernel, from an empty environment), ACCEPTED_EMPTY (other programs, from an empty environment)
# and ACCEPTED_PRELUDE (other programs, on top of a prelude built into them) to the names of
# the tools that accepted it. scripts/selftest.sh shows what each tool starts from.
# Each tool is started in an empty directory with an empty environment, and is
# given the export (for nanoda: a configuration naming it) and nothing else.
# Needs N_RECORDS, N_RECORDS_QUOT and N_CONSTANTS, the contents of the export
# as counted by scripts/export_census.py.
check_export() {
  ce_step="$1"; ce_file="$2"; ce_hard="$3"
  ACCEPTED_KERNEL=""; ACCEPTED_EMPTY=""; ACCEPTED_PRELUDE=""
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
  # name | executable | kind: kernel or separate | starts from: source (an empty environment,
  # read in its source), observed (an empty environment, observed) or prelude | what the number
  # in its success line counts | arguments before the file | pattern of the success line | what
  # is known of it
  while IFS='|' read -r ce_name ce_exe ce_kind ce_from ce_count ce_args ce_pattern ce_what; do
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
    case "$ce_from" in
      source)
        ce_start_text="an empty environment (its source creates one, \`Lean.mkEmptyEnvironment\`, and replays the export into it)" ;;
      observed)
        ce_start_text="an empty environment, as far as observed: it refuses a small export from which the declaration of Eq has been removed (scripts/selftest.sh repeats the observation); its source was not read" ;;
      *)
        ce_start_text="NOT an empty environment: its --help says that every run first installs a prelude that is built into the program (Eq, Nat, Empty, False, Quot, Bool, And), and it accepts a small export from which the declaration of Eq has been removed (scripts/selftest.sh repeats the observation). Its --help also says that a declaration of the export that copies one of the prelude is dropped when it is the same and makes the run fail when it differs; that was not examined" ;;
    esac
    {
      echo "  $ce_name"
      echo "    kind:        $ce_kind_text"
      echo "    starts from: $ce_start_text"
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
      if [ "$ce_from" = prelude ]; then
        ACCEPTED_PRELUDE="$ACCEPTED_PRELUDE${ACCEPTED_PRELUDE:+, }$ce_name"
      elif [ "$ce_kind" = kernel ]; then
        ACCEPTED_KERNEL="$ACCEPTED_KERNEL${ACCEPTED_KERNEL:+, }$ce_name"
      else
        ACCEPTED_EMPTY="$ACCEPTED_EMPTY${ACCEPTED_EMPTY:+, }$ce_name"
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
leanchecker|leanchecker|kernel|source|none|--from-export|^Lean default kernel accepts the solution$|its source is in the toolchain (src/lean/LeanChecker.lean): it reads the export and sends every declaration in it to Lean's kernel, starting from an empty environment
leanchecker-paranoid|leanchecker-paranoid|kernel|observed|none|--from-export|^Lean default kernel accepts the solution$|an executable of its own with the same options and messages as leanchecker (on arm64 macOS it is linked statically, where leanchecker uses the toolchain's shared libraries); the toolchain does not say what else its build changes, so it is not counted as an independent implementation
lean4lean|lean4lean|separate|observed|records-quot|--import|^checked [0-9]+ declarations$|the toolchain's LICENSES file attributes lean4lean to Mario Carneiro; the executable contains code named Lean4Lean.TypeChecker; its source is not in the toolchain and was not read
nanoda|nanoda_bin|separate|observed|constants||^Checked [0-9]+ declarations with no errors|its --help calls it an external type checker for Lean 4 (nanoda_lib); the toolchain's LICENSES file attributes nanoda to Chris Bailey; its source is not in the toolchain and was not read
con-leche|con-leche|separate|prelude|records|--jobs=4|^con-leche: accepted [0-9]+ declarations \(--verified\)$|the toolchain's LICENSES file attributes con-leche to the Lean FRO; its --help says that in this mode (--verified, the default) a file that declares a theorem of type False is never accepted, by a theorem about the program (ConLeche.no_False_declaration); neither its source nor that theorem was examined
con-ron|con-ron|separate|prelude|records|--jobs=4|^con-ron: accepted [0-9]+ declarations \(--verified\)$|the toolchain's LICENSES file attributes con-ron to the Lean FRO; its --help describes it as con-leche's checker written in Rust, so it is not a design independent of con-leche; its source was not examined
EOF
}

export_library() {   # the names are passed as arguments, one per declaration
  set --
  while IFS= read -r name; do set -- "$@" "$name"; done <"$TMP/lists/constants.txt"
  lake_ env "$TCBIN/leanexport" "$LIBRARY" -- "$@" >"$TMP/library.ndjson" 2>"$TMP/export.log"
}

echo "== 8. leanexport: the library's declarations and everything they depend on =="
START="$(date +%s)"
{
  echo
  echo "2. Export of the declarations of the library with everything they depend on"
  echo "  tool:    $(tool_id leanexport)"
  echo "  command: lake env leanexport $LIBRARY -- <the $N_CHECKABLE declaration names>"
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

echo "== 9. the export re-checked by the checkers =="
{
  echo
  echo "3. The export re-checked"
  echo "  Each tool is started in an empty directory with an empty environment (LEAN_ABORT_ON_PANIC=1"
  echo "  apart) and is given the export file and nothing else. A tool passes if it exits with status"
  echo "  0 and prints its line of acceptance; where that line says how many declarations were"
  echo "  checked, the number must be the one that scripts/export_census.py finds in the export."
  echo "  What a tool starts from is said for each: an empty environment, or a prelude of its own."
} >>"$RECORD"
if [ "$EXPORT" = ok ]; then
  N_RECORDS="$(sed -n 's/^declaration records: \([0-9][0-9]*\) .*/\1/p' "$TMP/census.txt")"
  N_RECORDS_QUOT="$(sed -n 's/^declaration records, the quotient records counted as one: //p' "$TMP/census.txt")"
  N_CONSTANTS="$(sed -n 's/^constants declared[^:]*: //p' "$TMP/census.txt")"
  check_export replay-export "$TMP/library.ndjson" true
  N_OUTSIDE="$(sed -n 's/^declarations from outside the library[^:]*: //p' "$TMP/census.txt")"
  if [ -n "$ACCEPTED_KERNEL$ACCEPTED_EMPTY$ACCEPTED_PRELUDE" ]; then
    REPLAYED="$REPLAYED (2) an export of the $N_CHECKABLE declarations of the library with the $N_OUTSIDE declarations of Mathlib, its dependencies and Lean core that they depend on: accepted from an empty environment by ${ACCEPTED_KERNEL:-no tool} (Lean's own kernel) and by ${ACCEPTED_EMPTY:-no tool} (programs that are not Lean's kernel); accepted on top of a prelude built into the program by ${ACCEPTED_PRELUDE:-no tool} (programs that are not Lean's kernel). All are run as the toolchain ships them."
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

# --- step 10 --------------------------------------------------------------
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
  echo "== 10. leanchecker --fresh: the whole imported environment, from an empty environment =="
  START="$(date +%s)"
  {
    echo "  tool:    $(tool_id leanchecker)"
    echo "  kind:    Lean's own kernel"
    echo "  command: lake env leanchecker --fresh $LIBRARY"
    echo "  does:    loads the compiled files of $LIBRARY and of every module it imports, directly"
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
    fail whole-env "leanchecker is not in the bin directory of the toolchain"
  else
    lake_ env "$TCBIN/leanchecker" --fresh "$LIBRARY" >"$TMP/fresh.log" 2>&1
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
