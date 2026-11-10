#!/usr/bin/env python3
"""Negative controls for the two text-level tools: `scripts/lean_scan.py` and
`scripts/gen_design.py`. Called by `scripts/selftest.sh`.

Usage:
    python3 scripts/selftest_static.py <project directory> <scratch directory>

Nothing is written into the project directory. Every case is a small file
written into the scratch directory, on which the real tool is run as a
subprocess. For each tool one line is printed, `PASS ...` or `FAIL ...`; a
FAIL is followed by the cases that did not behave as required. Exit status 1
if a line is FAIL.

The scratch directory is addressed by a relative path (the tools are run
with it as the working directory), because `gen_design.py` rightly refuses a
JSON path containing `/-`, and temporary directories can have such names.
"""
import copy
import json
import subprocess
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# lean_scan.py: (name, Lean text, substrings that must appear in the report).
# An empty list means the scan must report nothing and exit 0.

SCAN_CASES = [
    ("clean_tricky_comments", """import Mathlib.Data.Real.Basic

/-! Module text: instance, macro, sorry, set_option, "quoted", «x», #eval, @[simp] -/

namespace VoltageToBit

/- block /- nested: axiom instance -/ still a comment: sorry -/
/-- doc comment that mentions notation and `native_decide` -- and a double dash -/
theorem t (x : Nat) : x = x := rfl -- trailing comment with sorry and "quotes"

/--/ for Lean this is a documentation comment that is still open here -/
theorem u : True := trivial

end VoltageToBit
""", []),
    ("clean_identifiers_containing_keywords", """theorem foo (h_instance sorry' macro_x : Nat) (elab? : Nat) :
    sorry'.succ = sorry'.succ := rfl
""", []),
    ("clean_modifiers_and_sections", """import Mathlib.Data.Real.Basic

open Set in
private theorem foo (x : Nat) : x = x := rfl

noncomputable section

protected noncomputable def bar : Nat := 0

end
""", []),
    ("code_after_nested_comment", """/- a /- b -/ c -/
theorem x : False := sorry
""", ["`sorry`"]),
    ("kernel_check_switched_off", """import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (.thmDecl {
  name := `Bad.bad, levelParams := [], type := mkConst ``False,
  value := mkConst ``True.intro }))
theorem Bad.oops : False := Bad.bad
""", ["`set_option`", "`run_cmd`", "import of `Lean`"]),
    ("comment_opener_after_subtype_bar", """theorem x : {n : Nat //-1 < 0} := sorry -- -/
""", ["comment opener `/-` directly after `/`", "`sorry`"]),
    ("comment_opener_after_bind_arrow", """def f : IO Nat := do
  let x <--sorry
  pure x
""", ["comment opener `--` directly after `<`", "`sorry`"]),
    ("string_literal", """def s : String := "-- " ++ toString (sorry : Nat)
""", ["double quote outside a comment", "`sorry`"]),
    ("escaped_identifier", """def «a -- b» : Nat := 1
""", ["escaped identifier"]),
    ("attribute", """@[simp] theorem foo : (1 : Nat) = 1 := rfl
""", ["`@[`"]),
    ("indented_instance", """theorem foo : True := trivial
  instance : Inhabited Nat := ⟨0⟩
""", ["`instance`"]),
    ("macro_command_of_mathlib", """alias bar := foo
""", ["column 0 starts with `alias`"]),
    ("instance_implicit_variable", """variable {D : Nat} [Fact False]
theorem foo : True := trivial
""", ["instance-implicit `variable`"]),
    ("keyword_glued_to_numeral", """theorem foo : Nat := 1sorry
""", ["glued to a numeral"]),
    ("keyword_before_projection", """theorem foo : Nat := sorry.1
""", ["`sorry`"]),
    ("keyword_after_prefix_operator", """theorem foo : Bool := !sorry
""", ["`sorry`"]),
    ("indented_command", """theorem foo : True := trivial
  variable [Fact False]
theorem bar : False := Fact.out
""", ["`variable` is not at the start of a line"]),
    ("second_command_on_one_line", """theorem foo : True := trivial variable [Fact False]
theorem bar : False := Fact.out
""", ["`variable` is not at the start of a line"]),
    ("indented_import", """  import Lean
theorem foo : True := trivial
""", ["`import` is not at the start of a line"]),
    ("declaration_after_other_text", """open Set in theorem foo : True := trivial
""", ["`theorem` is not at the start of a line"]),
    ("hash_command", """theorem foo : True := trivial
#exit
theorem bar : False := trivial
""", ["`#` command"]),
    ("decide_native", """theorem foo : 2 + 2 = 4 := by decide +native
""", ["`+native`"]),
    ("unterminated_comment", """theorem foo : True := trivial
/- never closed
theorem bar : False := sorry
""", ["unterminated comment", "`sorry`"]),
    ("axiom_declaration", """axiom anything : False
""", ["`axiom`"]),
    ("partial_definition", """partial def loop (n : Nat) : Nat := loop (n + 1)
""", ["`partial`"]),
    ("notation", """local notation "⊥⊥" => False
""", ["`notation`"]),
]

LAKEFILE_CASES = [
    ("lakefile_kernel_option", "[leanOptions]\n", "[leanOptions]\ndebug.skipKernelTC = true\n",
     "debug.skipKernelTC = true"),
    ("lakefile_auto_implicit", "autoImplicit = false", "autoImplicit = true", "autoImplicit = true"),
    ("lakefile_extra_args", '[[lean_lib]]\nname = "VoltageToBit"',
     '[[lean_lib]]\nname = "VoltageToBit"\nmoreLeanArgs = ["-Ddebug.skipKernelTC=true"]',
     "moreLeanArgs"),
]


def run(cmd, cwd):
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def test_scan(project, scratch):
    scan = str(project / "scripts" / "lean_scan.py")
    failures = []
    flagged = clean = 0
    for name, text, expected in SCAN_CASES:
        rel = Path("scan") / f"{name}.lean"
        (scratch / rel).parent.mkdir(parents=True, exist_ok=True)
        (scratch / rel).write_text(text, encoding="utf-8")
        code, output = run([sys.executable, scan, str(rel)], scratch)
        if expected:
            flagged += 1
            missing = [e for e in expected if e not in output]
            if code != 1 or missing:
                failures.append(f"{name}: exit {code}, not reported: {missing}")
        else:
            clean += 1
            if code != 0 or "no forbidden construct found" not in output:
                failures.append(f"{name}: clean text was flagged (exit {code}): {output.strip()[:300]}")
    original = (project / "lakefile.toml").read_text(encoding="utf-8")
    rel = Path("scan") / "empty.lean"
    (scratch / rel).write_text("", encoding="utf-8")
    lake_dir = scratch / "scan" / "lake"
    lake_dir.mkdir(parents=True, exist_ok=True)
    (lake_dir / "lakefile.toml").write_text(original, encoding="utf-8")
    code, output = run([sys.executable, scan, "--lakefile", "scan/lake/lakefile.toml", str(rel)], scratch)
    clean += 1
    if code != 0:
        failures.append(f"lakefile_unchanged: the project's own lakefile.toml was flagged: {output.strip()[:300]}")
    for name, old, new, expected in LAKEFILE_CASES:
        flagged += 1
        if old not in original:
            failures.append(f"{name}: the lakefile no longer contains {old!r}; update this case")
            continue
        (lake_dir / "lakefile.toml").write_text(original.replace(old, new, 1), encoding="utf-8")
        code, output = run([sys.executable, scan, "--lakefile", "scan/lake/lakefile.toml", str(rel)], scratch)
        if code != 1 or expected not in output:
            failures.append(f"{name}: exit {code}, not reported: {expected!r}")
    return ("the source scan flags each of %d texts that contain a forbidden construct or defeat "
            "comment detection, and none of %d clean texts" % (flagged, clean)), failures


# ---------------------------------------------------------------------------
# gen_design.py: each case modifies a copy of the committed design record.

def design_cases(base):
    def changed(path, value):
        record = copy.deepcopy(base)
        target = record
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        return json.dumps(record, ensure_ascii=False, indent=2)

    def removed(path):
        record = copy.deepcopy(base)
        target = record
        for key in path[:-1]:
            target = target[key]
        del target[path[-1]]
        return json.dumps(record, ensure_ascii=False, indent=2)

    good = json.dumps(base, ensure_ascii=False, indent=2)
    injection = "ILLUSTRATIVE -/\ntheorem injected_from_json : True := trivial\n/-- resumed comment"
    cases = [
        # the five inputs of review/tooling/gen_design_probe.py
        ("number_with_trailing_newline", changed(["eps"], "2\n")),
        ("number_with_non_ascii_digit", changed(["eps"], "٢")),
        ("status_closes_the_comment", changed(["status"], injection)),
        ("duplicate_key", good.replace('"eps": "2"', '"eps": "2",\n  "eps": "1"', 1)),
        ("inverted_box_range", changed(["box", "kn"], ["300", "240"])),
        # more of the same kinds
        ("status_opens_a_comment", changed(["status"], "see /- here")),
        ("status_with_newline", changed(["status"], "one\ntwo")),
        ("status_with_bidi_override", changed(["status"], "abc‮def")),
        ("status_not_a_string", changed(["status"], 5)),
        ("name_with_backquote", changed(["name"], "a`b")),
        ("name_with_comment_end", changed(["name"], "a-/b")),
        ("name_with_space", changed(["name"], "a b")),
        ("duplicate_nested_key", good.replace('"VIL": "0.40"', '"VIL": "0.40",\n    "VIL": "0.10"', 1)),
        ("duplicate_key_by_escape", good.replace('"eps": "2"', '"eps": "2",\n  "\\u0065ps": "1"', 1)),
        ("missing_key", removed(["eps"])),
        ("missing_nested_key", removed(["thresholds", "VOH"])),
        ("unknown_key", changed(["extra"], "1")),
        ("unknown_nested_key", changed(["thresholds", "VXX"], "1")),
        ("units_other_than_the_docstring_says", changed(["units", "voltage"], "mV")),
        ("number_as_json_number", changed(["eps"], 2)),
        ("number_with_plus_sign", changed(["eps"], "+2")),
        ("number_with_exponent", changed(["eps"], "2e0")),
        ("number_with_leading_space", changed(["eps"], " 2")),
        ("number_without_integer_part", changed(["eps"], ".5")),
        ("number_without_fraction_digits", changed(["eps"], "2.")),
        ("number_with_fullwidth_digit", changed(["eps"], "２")),
        ("number_hexadecimal", changed(["eps"], "0x10")),
        ("number_with_lean_code", changed(["eps"], "2\n\ntheorem injected : True := trivial")),
        ("box_range_with_three_entries", changed(["box", "kn"], ["160", "200", "240"])),
        ("box_range_not_a_list", changed(["box", "kn"], "160")),
        ("inverted_safe_domain", changed(["safe_domain", "Vlo"], "3")),
        ("inverted_input_thresholds", changed(["thresholds", "VIL"], "1.30")),
        ("not_an_object", "[1, 2, 3]"),
        ("not_json", "{"),
        ("nan_constant", good.replace('"eps": "2"', '"eps": NaN', 1)),
    ]
    assert all(text != good for _, text in cases), "a case does not modify the record"
    return good, cases


def test_generator(project, scratch):
    gen = str(project / "scripts" / "gen_design.py")
    base = json.loads((project / "designs" / "illustrative-1v8.json").read_text(encoding="utf-8"))
    good, cases = design_cases(base)
    out_dir = scratch / "gen"
    out_dir.mkdir(parents=True, exist_ok=True)
    failures = []

    # positive controls: the committed record is in sync, and a re-serialised
    # valid record is accepted (so the rejections below are due to the change)
    code, output = run([sys.executable, gen, "--check", "designs/illustrative-1v8.json",
                        "VoltageToBit/Examples/IllustrativeDesign.lean", "illustrative"], project)
    if code != 0:
        failures.append(f"--check on the committed record: exit {code}: {output.strip()[:200]}")
    (out_dir / "good.json").write_text(good, encoding="utf-8")
    code, output = run([sys.executable, gen, "gen/good.json", "gen/good.lean", "illustrative"], scratch)
    if code != 0 or not (out_dir / "good.lean").exists():
        failures.append(f"a valid record was rejected: exit {code}: {output.strip()[:200]}")

    for name, text in cases:
        (out_dir / f"{name}.json").write_text(text, encoding="utf-8")
        code, output = run([sys.executable, gen, f"gen/{name}.json", f"gen/{name}.lean", "illustrative"],
                           scratch)
        if code != 2 or "REJECTED" not in output or (out_dir / f"{name}.lean").exists():
            failures.append(f"{name}: exit {code}, output written: {(out_dir / f'{name}.lean').exists()}")
    arg_cases = [
        ("definition_name_with_lean_code", ["gen/good.json", "gen/arg1.lean", "x : True := trivial\ndef y"]),
        ("json_path_with_comment_opener", ["gen/-x/../good.json", "gen/arg2.lean", "illustrative"]),
    ]
    (out_dir / "-x").mkdir(exist_ok=True)
    for name, args in arg_cases:
        code, output = run([sys.executable, gen] + args, scratch)
        if code != 2 or "REJECTED" not in output or (scratch / args[1]).exists():
            failures.append(f"{name}: exit {code}")
    # stale detection
    (out_dir / "stale.lean").write_text((out_dir / "good.lean").read_text(encoding="utf-8").replace(
        "eps := 2", "eps := 3"), encoding="utf-8")
    code, output = run([sys.executable, gen, "--check", "gen/good.json", "gen/stale.lean", "illustrative"],
                       scratch)
    if code != 1 or "STALE" not in output:
        failures.append(f"a generated file with one changed number was not reported stale (exit {code})")

    # --check-all: generated files are found by their header, design files by their directory
    def write_exact(path, text):
        with open(path, "w", encoding="utf-8", newline="") as handle:
            handle.write(text)

    def check_all(designs, expected_code, expected_text, what):
        code, output = run([sys.executable, gen, "--check-all", designs, "all/lean"], scratch)
        if code != expected_code or expected_text not in output:
            failures.append(f"--check-all, {what}: exit {code}: {output.strip()[:300]}")

    every = scratch / "all"
    for sub in ("designs", "empty", "lean/Sub"):
        (every / sub).mkdir(parents=True, exist_ok=True)
    write_exact(every / "designs" / "one.json", good)
    write_exact(every / "lean" / "Other.lean", "theorem unrelated : True := trivial\n")
    run([sys.executable, gen, "all/designs/one.json", "all/lean/Sub/One.lean", "one"], scratch)
    check_all("all/designs", 0, "ok: all/lean/Sub/One.lean matches all/designs/one.json",
              "one record in sync")
    write_exact(every / "designs" / "two.json", good)
    check_all("all/designs", 1,
              "NOT IN SYNC: no Lean file under all/lean is the generated form of all/designs/two.json",
              "a design file that nothing was generated from")
    run([sys.executable, gen, "all/designs/two.json", "all/lean/Two.lean", "two"], scratch)
    check_all("all/designs", 0, "ok: all/lean/Two.lean matches all/designs/two.json",
              "two records in sync")
    one = every / "lean" / "Sub" / "One.lean"
    original = one.read_text(encoding="utf-8") if one.exists() else ""
    if "eps := 2" not in original or "from all/designs/one.json" not in original:
        failures.append("--check-all: the generated file does not have the expected form; update these cases")
    write_exact(one, original.replace("eps := 2", "eps := 3"))
    check_all("all/designs", 1, "STALE: all/lean/Sub/One.lean does not match all/designs/one.json",
              "a generated file with one changed number")
    write_exact(one, original.replace("from all/designs/one.json", "from gen/good.json"))
    check_all("all/designs", 1, "which is not one of the JSON files in all/designs",
              "a generated file whose header names a JSON file elsewhere")
    write_exact(one, original.replace("GENERATED by", "Generated by"))
    check_all("all/designs", 1,
              "NOT IN SYNC: no Lean file under all/lean is the generated form of all/designs/one.json",
              "a generated file whose header was altered")
    write_exact(one, original)
    write_exact(every / "designs" / "two.json", dict(cases)["duplicate_key"])
    check_all("all/designs", 2, "REJECTED", "a design file that is rejected")
    check_all("all/empty", 1, "NO DESIGN RECORD", "a directory without design files")
    code, output = run([sys.executable, gen, "--check-all", "designs", "VoltageToBit"], project)
    if code != 0 or "ok: " not in output:
        failures.append(f"--check-all on the committed project: exit {code}: {output.strip()[:200]}")
    return ("the design generator rejects each of %d malformed inputs, writes nothing for them, "
            "accepts the committed record, and reports a changed output as stale; --check-all "
            "also reports a design file without a generated file and a generated file whose "
            "header was altered" % (len(cases) + len(arg_cases))), failures


def main(argv):
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    project, scratch = Path(argv[0]).resolve(), Path(argv[1]).resolve()
    scratch.mkdir(parents=True, exist_ok=True)
    status = 0
    for label, test in (("scan", test_scan), ("generator", test_generator)):
        description, failures = test(project, scratch)
        if failures:
            status = 1
            print(f"FAIL {label}: {description}")
            for failure in failures:
                print(f"       {failure}")
        else:
            print(f"PASS {label}: {description}")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
