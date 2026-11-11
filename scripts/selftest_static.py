#!/usr/bin/env python3
"""Negative controls for the source scan (`scripts/SourceScan.lean`) and for the
design generator (`scripts/gen_design.py`). Called by `scripts/selftest.sh`.

Usage:
    python3 scripts/selftest_static.py <project directory> <scratch directory>

Nothing is written into the project directory. Every case is a small file
written into the scratch directory, on which the real tool is run. For each
tool one line is printed, `PASS ...` or `FAIL ...`; a FAIL is followed by the
cases that did not behave as required. Exit status 1 if a line is FAIL.

The scan cases are read by Lean's own parser, like the library, each in a
process of its own. The scan does not elaborate declarations, so the names in
a case need not exist. `{MATHLIB}` in a case stands for a Mathlib module that
the library itself imports (found in the sources, so nothing is hard-coded and
nothing has to be compiled for the test). The project's build must be up to
date.

The scratch directory is addressed by a relative path where `gen_design.py`
is concerned (it is run with the scratch directory as its working directory),
because it rightly refuses a JSON path containing `/-`, and temporary
directories can have such names.
"""
import copy
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# SourceScan.lean: (name, Lean text, substrings that must appear in the report
# of that file). An empty list means the scan must report no finding.

BYPASS = """set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (.thmDecl {
  name := `Bad.bad, levelParams := [], type := mkConst ``False,
  value := mkConst ``True.intro }))
theorem Bad.oops : False := Bad.bad
"""

SCAN_CASES = [
    # --- clean texts: what the library is written in
    ("clean_tricky_comments", """/-! Module text: instance, macro, sorry, set_option, "quoted", #eval, @[simp] -/

namespace Selftest

/- block /- nested: axiom instance -/ still a comment: sorry -/
/-- doc comment that mentions notation and `native_decide` -- and a double dash -/
theorem t (x : Nat) : x = x := rfl -- trailing comment with sorry and "quotes"

/--/ for Lean this is a documentation comment that is still open here -/
theorem u : True := trivial

end Selftest
""", []),
    ("clean_identifiers_containing_keywords", """theorem foo (h_instance sorry' macro_x : Nat) (elab? : Nat) :
    sorry' = sorry' := rfl
""", []),
    ("clean_library_style", """import {MATHLIB}

/-! A file in the style of the library. -/

open Set

namespace Selftest

variable {a b : Nat} (c : Nat)

/-- A structure. -/
structure Pair where
  left : Nat
  right : Nat

private theorem foo (x : Nat) (h : 0 < x) : x = x := by
  have h2 : x = x := rfl
  exact h2

noncomputable def bar : Nat := 0

end Selftest
""", []),
    # --- B2: what Lean reads as code is seen as code
    ("b2_slash_dash_slash", """/-/-/
theorem bad : False := sorry
-- -/ -/
""", ["b2_slash_dash_slash.lean:2:", "`Lean.Parser.Term.sorry`"]),
    ("b2_hidden_scoped_instance", """namespace Selftest

/-/-/
scoped instance fakeLE : LE Nat := ⟨fun _ _ => True⟩
-- -/ -/

theorem everything_is_small (x y : Nat) : x ≤ y := trivial

end Selftest
""", ["b2_hidden_scoped_instance.lean:4:", "`Lean.Parser.Command.instance`", "`Lean.Parser.Term.scoped`"]),
    ("b2_hidden_bypass", "/-/-/\nimport Lean\nopen Lean Elab Command\n" + BYPASS + "-- -/ -/\n",
     ["import of `Lean`", "`Lean.Parser.Command.set_option`", "`Lean.runCmd`"]),
    ("code_after_nested_comment", """/- a /- b -/ c -/
theorem x : False := sorry
""", ["`Lean.Parser.Term.sorry`"]),
    ("comment_opener_after_subtype_bar", """theorem x : {n : Nat //-1 < 0} := sorry -- -/
""", ["`Lean.Parser.Term.sorry`"]),
    ("unterminated_comment", """theorem foo : True := trivial
/- never closed
theorem bar : False := sorry
""", ["[parse]", "unterminated comment"]),
    # --- the kernel bypass of the review, and other ways of running code
    ("kernel_check_switched_off", "import Lean\nopen Lean Elab Command\n" + BYPASS,
     ["import of `Lean`", "a command of kind `Lean.Parser.Command.in`",
      "`Lean.Parser.Command.set_option`", "`Lean.runCmd`"]),
    ("eval_command", """#eval 1 + 1
""", ["a command of kind `Lean.Parser.Command.eval`"]),
    ("initialize_command", """initialize pure ()
""", ["a command of kind `Lean.Parser.Command.initialize`"]),
    ("m8_tactic_configuration", """import {MATHLIB}

theorem helper (x : Int) (h : 0 < x) : 0 ≤ x := by
  linarith (oracle := { produceCertificate := fun hyps maxVar => default })
""", ["`Lean.Parser.Tactic.valConfigItem`"]),
    ("decide_native_plus", """theorem foo : 2 + 2 = 4 := by decide +native
""", ["`Lean.Parser.Tactic.posConfigItem`"]),
    ("decide_native_config", """theorem foo : 2 + 2 = 4 := by decide (native := true)
""", ["`Lean.Parser.Tactic.valConfigItem`"]),
    ("native_decide", """theorem foo : 2 + 2 = 4 := by native_decide
""", ["`Lean.Parser.Tactic.nativeDecide`"]),
    ("by_elab", """theorem foo : True := by_elab pure (Lean.mkConst ``True.intro)
""", ["is not on the allow-list"]),
    ("hash_exit", """theorem foo : True := trivial
#exit
theorem bar : False := trivial
""", ["a command of kind `Lean.Parser.Command.exit`", "Lean stops reading the file at this command"]),
    ("import_in_the_middle", """theorem foo : True := trivial
import Lean
""", ["a command of kind `Lean.Parser.Command.import`"]),
    # --- constructs that change what later text means
    ("attribute_on_declaration", """@[simp] theorem foo : (1 : Nat) = 1 := rfl
""", ["`Lean.Parser.Term.attributes`"]),
    ("attribute_command", """theorem foo : (1 : Nat) = 1 := rfl
attribute [simp] foo
""", ["a command of kind `Lean.Parser.Command.attribute`"]),
    ("indented_instance", """theorem foo : True := trivial
  instance : Inhabited Nat := ⟨0⟩
""", ["indented_instance.lean:2:", "`Lean.Parser.Command.instance`"]),
    ("notation", """local notation "<<>>" => False
""", ["a command of kind `Lean.Parser.Command.notation`"]),
    ("infix", """infixl:65 " +++ " => Nat.add
""", ["a command of kind `Lean.Parser.Command.mixfix`"]),
    ("macro", """macro "mytriv" : tactic => `(tactic| trivial)
""", ["a command of kind `Lean.Parser.Command.macro`"]),
    ("syntax", """syntax "mything" : term
""", ["a command of kind `Lean.Parser.Command.syntax`"]),
    ("elab", """elab "myelab" : term => pure (Lean.mkConst ``True)
""", ["a command of kind `Lean.Parser.Command.elab`"]),
    ("set_option_command", """set_option autoImplicit true
theorem foo (h : a = b) : b = a := h.symm
""", ["a command of kind `Lean.Parser.Command.set_option`"]),
    ("set_option_in_tactic", """theorem foo : True := by
  set_option maxRecDepth 2 in trivial
""", ["`Lean.Parser.Tactic.set_option`"]),
    ("open_in_command", """open Nat in theorem foo : True := trivial
""", ["a command of kind `Lean.Parser.Command.in`"]),
    ("open_in_term", """theorem foo : open Nat in True := trivial
""", ["`Lean.Parser.Term.open`"]),
    ("open_hiding", """open Nat hiding add
""", ["`Lean.Parser.Command.openHiding`"]),
    ("open_renaming", """open Nat renaming add → plus
""", ["`Lean.Parser.Command.openRenaming`"]),
    ("export_command", """export Nat (add)
""", ["a command of kind `Lean.Parser.Command.export`"]),
    ("section_command", """section
theorem foo : True := trivial
end
""", ["a command of kind `Lean.Parser.Command.section`"]),
    ("mutual_block", """mutual
theorem a : True := trivial
theorem b : True := trivial
end
""", ["a command of kind `Lean.Parser.Command.mutual`"]),
    ("deriving_clause", """structure P where
  x : Nat
deriving Repr
""", ["`Lean.Parser.Command.derivingClass`"]),
    ("where_declarations", """def f : Nat := g
where g := 1
""", ["`Lean.Parser.Term.whereDecls`"]),
    # --- hidden hypotheses and universes
    ("instance_implicit_variable", """variable {D : Nat} [Fact False]
theorem foo : True := trivial
""", ["[variable]", "`Lean.Parser.Term.instBinder`"]),
    ("s4_indented_variable_question", """import {MATHLIB}

theorem foo : True := trivial
  variable? [Inhabited Empty]

theorem looksFalse : False := (default : Empty).elim
""", ["s4_indented_variable_question.lean:4:3:", "a command of kind `Mathlib.Command.Variable.variable?`"]),
    ("second_command_on_one_line", """theorem foo : True := trivial variable [Fact False]
theorem bar : False := Fact.out
""", ["[variable]"]),
    ("include_command", """variable (h : False)
include h
theorem foo : False := h
""", ["a command of kind `Lean.Parser.Command.include`"]),
    ("instance_binder_in_statement", """theorem foo [Inhabited Empty] : False := (default : Empty).elim
""", ["`Lean.Parser.Term.instBinder`"]),
    ("binder_with_tactic_default", """theorem foo (h : False := by trivial) : False := h
""", ["`Lean.Parser.Term.binderTactic`"]),
    ("structure_instance_field", """structure S where
  [inst : Inhabited Empty]
""", ["`Lean.Parser.Command.structInstBinder`"]),
    ("explicit_application", """theorem foo : @Eq Nat 1 1 := rfl
""", ["`Lean.Parser.Term.explicit`"]),
    ("universe_command", """universe u
""", ["a command of kind `Lean.Parser.Command.universe`"]),
    ("universe_parameters", """theorem foo.{u} (x : Nat) : x = x := rfl
""", ["[universe]"]),
    ("sort_in_statement", """theorem foo (T : Sort _) : True := trivial
""", ["`Lean.Parser.Term.sort`"]),
    # --- declarations of other kinds
    ("axiom_declaration", """axiom anything : False
""", ["`Lean.Parser.Command.axiom`"]),
    ("opaque_declaration", """opaque hidden : Nat
""", ["`Lean.Parser.Command.opaque`"]),
    ("partial_definition", """partial def loop (n : Nat) : Nat := loop (n + 1)
""", ["`Lean.Parser.Command.partial`"]),
    ("unsafe_definition", """unsafe def cast (n : Nat) : Nat := n
""", ["`Lean.Parser.Command.unsafe`"]),
    ("abbrev_declaration", """abbrev N := Nat
""", ["`Lean.Parser.Command.abbrev`"]),
    ("class_declaration", """class C (n : Nat) where
  x : Nat
""", ["`Lean.Parser.Command.classTk`"]),
    ("example_declaration", """example : True := trivial
""", ["`Lean.Parser.Command.example`"]),
    ("sorry_as_term", """theorem foo : False := sorry
""", ["`Lean.Parser.Term.sorry`"]),
    ("sorry_glued_to_numeral", """theorem foo : Nat := 1sorry
""", ["[parse]"]),
    ("sorry_as_tactic", """theorem foo : False := by sorry
""", ["`Lean.Parser.Tactic.tacticSorry`"]),
    ("string_literal", """def s : String := "-- " ++ toString (1 : Nat)
""", ["syntax of kind `str`"]),
    ("quotation", """def q := `(1)
""", ["`Lean.Parser.Term.quot`"]),
    # --- the header
    ("header_module", """module

theorem foo : True := trivial
""", ["[header] `module`"]),
    ("header_prelude", """prelude
""", ["[header] `prelude`"]),
    ("header_import_all", """import all Lean
""", ["[header] `public`, `meta` or `all` on an import"]),
    ("header_indented_import", """  import Lean
theorem foo : True := trivial
""", ["import of `Lean`"]),
    ("header_two_imports_one_line", """import Init import Lean
""", ["import of `Init`", "import of `Lean`"]),
    # --- the text itself
    ("text_tab", "theorem foo : True :=\n\ttrivial\n", ["character U+0009"]),
    ("text_crlf", "theorem foo : True := trivial\r\ntheorem bar : True := trivial\r\n", ["character U+000D"]),
    ("text_byte_order_mark", "﻿theorem foo : True := trivial\n", ["character U+FEFF"]),
    ("text_bidi_override_in_comment", "/- a comment ‮ that turns the text around -/\ntheorem foo : True := trivial\n",
     ["character U+202E"]),
    ("text_lookalike_letter", "theorem fоo : True := trivial\n", ["character U+043E"]),
    ("text_escaped_identifier", "def «a -- b» : Nat := 1\n", ["character U+00AB"]),
    ("text_lang_line", "#lang lean4\ntheorem foo : True := trivial\n", ["starts with `#lang`"]),
    ("text_code_far_right", "theorem foo : True" + " " * 150 + "∧ True := sorry\n", ["[column]"]),
]


def run(cmd, cwd, env=None):
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env)
    return proc.returncode, proc.stdout + proc.stderr


def library_mathlib_import(project):
    """A Mathlib module that the library imports itself."""
    for path in sorted((project / "VoltageToBit").rglob("*.lean")):
        for line in path.read_text(encoding="utf-8").split("\n"):
            match = re.fullmatch(r"import (Mathlib\.[A-Za-z0-9_.]+)", line)
            if match:
                return match.group(1)
    return None


def test_scan(project, scratch):
    failures = []
    flagged = sum(1 for _, _, expected in SCAN_CASES if expected)
    clean = len(SCAN_CASES) - flagged
    description = ("the source scan (Lean's own parser) reports each of %d texts that contain a construct "
                   "outside the allow-list or a way of hiding one, at the kind or character named in the "
                   "case, and reports nothing for %d texts in the style of the library" % (flagged, clean))
    mathlib = library_mathlib_import(project)
    if mathlib is None:
        return description, ["no `import Mathlib...` line in the library; update the cases that need one"]
    case_dir = scratch / "scan"
    case_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    for name, text, _ in SCAN_CASES:
        path = case_dir / f"{name}.lean"
        with open(path, "w", encoding="utf-8", newline="") as handle:
            handle.write(text.replace("{MATHLIB}", mathlib))
        paths.append(str(path))
    # compile the scan program once, then run it on all cases (as scripts/check.sh does)
    lib = scratch / "scanlib"
    lib.mkdir(parents=True, exist_ok=True)
    code, output = run(["lake", "env", "lean", "--root=scripts", "-o", str(lib / "SourceScan.olean"),
                        "scripts/SourceScan.lean"], project)
    if code != 0:
        return description, [f"scripts/SourceScan.lean does not compile: {output.strip()[:400]}"]
    main = scratch / "scan-main.lean"
    main.write_text("import SourceScan\n", encoding="utf-8")
    jobs = os.environ.get("CHECK_SCAN_JOBS", "2")
    code, output = run(["lake", "env", "sh", "-c",
                        'lib="$1"; main="$2"; jobs="$3"; shift 3; LEAN_PATH="$lib:$LEAN_PATH" exec lean --run "$main" '
                        'texts --self "$main" --allow scripts/allowlist.txt --root VoltageToBit --jobs "$jobs" "$@"',
                        "sh", str(lib), str(main), jobs] + paths, project)
    reports = {}
    current = None
    for line in output.split("\n"):
        if line.startswith("== "):
            current = line[3:]
            reports[current] = []
        elif current is not None:
            reports[current].append(line)
    any_flagged = False
    for (name, _, expected), path in zip(SCAN_CASES, paths):
        report = "\n".join(reports.get(path, ["<no report for this file>"]))
        if expected:
            any_flagged = True
            missing = [e for e in expected if e not in report]
            if missing or "no finding" in report.split("\n"):
                failures.append(f"{name}: not reported: {missing}; the scan said: {report.strip()[:300]}")
        elif report.strip() != "no finding":
            failures.append(f"{name}: a clean text was flagged: {report.strip()[:300]}")
    if code != (1 if any_flagged else 0):
        failures.append(f"the scan exited with status {code}: {output.strip()[-300:]}")
    return description, failures


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
    # an output file that cannot be written: exit status 2 and a message, no traceback
    code, output = run([sys.executable, gen, "gen/good.json", "gen/no-such-directory/out.lean", "illustrative"],
                       scratch)
    if code != 2 or "cannot write" not in output or "Traceback" in output:
        failures.append(f"an output path that cannot be written: exit {code}: {output.strip()[:200]}")
    # stale detection
    (out_dir / "stale.lean").write_text((out_dir / "good.lean").read_text(encoding="utf-8").replace(
        "eps := 2", "eps := 3"), encoding="utf-8")
    code, output = run([sys.executable, gen, "--check", "gen/good.json", "gen/stale.lean", "illustrative"],
                       scratch)
    if code != 1 or "STALE" not in output:
        failures.append(f"a generated file with one changed number was not reported stale (exit {code})")

    # --check-all: the design records are the ones named in the list, whatever a file says
    def write_exact(path, text):
        with open(path, "w", encoding="utf-8", newline="") as handle:
            handle.write(text)

    def check_all(designs, listing, expected_code, expected_texts, what):
        write_exact(every / "records.txt", "# design records\n" + "".join(line + "\n" for line in listing))
        code, output = run([sys.executable, gen, "--check-all", designs, "all/lean", "all/records.txt"], scratch)
        missing = [text for text in expected_texts if text not in output]
        if code != expected_code or missing:
            failures.append(f"--check-all, {what}: exit {code}, not reported: {missing}: {output.strip()[:300]}")

    every = scratch / "all"
    for sub in ("designs", "empty", "lean/Sub"):
        (every / sub).mkdir(parents=True, exist_ok=True)
    one_line = "all/designs/one.json  all/lean/Sub/One.lean  one"
    two_line = "all/designs/two.json  all/lean/Two.lean  two"
    write_exact(every / "designs" / "one.json", good)
    write_exact(every / "lean" / "Other.lean", "theorem unrelated : True := trivial\n")
    run([sys.executable, gen, "all/designs/one.json", "all/lean/Sub/One.lean", "one"], scratch)
    check_all("all/designs", [one_line], 0,
              ["ok: all/lean/Sub/One.lean is what all/designs/one.json generates with the definition name one"],
              "one record in sync")
    write_exact(every / "designs" / "two.json", good)
    check_all("all/designs", [one_line], 1,
              ["NOT LISTED: all/designs/two.json is a JSON design file, but all/records.txt does not name it"],
              "a design file that the list does not name")
    run([sys.executable, gen, "all/designs/two.json", "all/lean/Two.lean", "two"], scratch)
    check_all("all/designs", [one_line], 1,
              ["NOT LISTED: all/lean/Two.lean begins with the header of a generated design record"],
              "a generated file that the list does not name")
    check_all("all/designs", [one_line, two_line], 0,
              ["ok: all/lean/Two.lean is what all/designs/two.json generates with the definition name two"],
              "two records in sync")
    one = every / "lean" / "Sub" / "One.lean"
    original = one.read_text(encoding="utf-8") if one.exists() else ""
    if "eps := 2" not in original or "from all/designs/one.json" not in original:
        failures.append("--check-all: the generated file does not have the expected form; update these cases")
    stale_one = "STALE: all/lean/Sub/One.lean is not what all/designs/one.json generates with the definition name one"
    write_exact(one, original.replace("eps := 2", "eps := 3"))
    check_all("all/designs", [one_line, two_line], 1, [stale_one], "a generated file with one changed number")
    write_exact(one, original.replace("from all/designs/one.json", "from gen/good.json"))
    check_all("all/designs", [one_line, two_line], 1, [stale_one],
              "a generated file whose header names a JSON file elsewhere")
    write_exact(one, original.replace("GENERATED by", "Generated by"))
    check_all("all/designs", [one_line, two_line], 1, [stale_one], "a generated file whose header was altered")
    # the decoy of verification round 4, issue 4: the header of the record altered, and a copy generated
    # from the same JSON file under another definition name in another file
    run([sys.executable, gen, "all/designs/one.json", "all/lean/Decoy.lean", "oneDecoy"], scratch)
    check_all("all/designs", [one_line, two_line], 1,
              [stale_one, "NOT LISTED: all/lean/Decoy.lean begins with the header of a generated design record"],
              "the record with its header altered and a generated copy under another name")
    write_exact(one, original)
    check_all("all/designs", [one_line, two_line], 1,
              ["NOT LISTED: all/lean/Decoy.lean begins with the header of a generated design record"],
              "a generated copy of a record under another name")
    (every / "lean" / "Decoy.lean").unlink()
    check_all("all/designs", ["all/designs/one.json  all/lean/Sub/One.lean  uno", two_line], 1,
              ["STALE: all/lean/Sub/One.lean is not what all/designs/one.json generates with the definition name uno"],
              "a list that names another definition")
    check_all("all/designs", [one_line, two_line, "all/designs/one.json  all/lean/Other.lean  other"], 1,
              ["LISTED TWICE: all/records.txt line 4 names all/designs/one.json"], "a JSON file named twice")
    check_all("all/designs", [one_line, two_line, "gen/good.json  all/lean/Other.lean  other"], 1,
              ["NOT A DESIGN FILE: all/records.txt line 4 names gen/good.json"], "a JSON file from elsewhere")
    check_all("all/designs", [one_line, "all/designs/two.json  all/lean/Three.lean  two"], 1,
              ["MISSING: all/records.txt line 3 names all/lean/Three.lean"], "a listed file that does not exist")
    check_all("all/designs", [one_line, two_line, "all/designs/three.json all/lean/Three.lean"], 2,
              ["REJECTED all/records.txt"], "a line of the list without a definition name")
    write_exact(every / "designs" / "two.json", dict(cases)["duplicate_key"])
    check_all("all/designs", [one_line, two_line], 2, ["REJECTED all/designs/two.json"],
              "a design file that is rejected")
    check_all("all/empty", [], 1, ["NO DESIGN RECORD"], "a directory without design files")
    code, output = run([sys.executable, gen, "--check-all", "designs", "VoltageToBit",
                        "scripts/design-records.txt"], project)
    if code != 0 or "ok: " not in output:
        failures.append(f"--check-all on the committed project: exit {code}: {output.strip()[:200]}")
    return ("the design generator rejects each of %d malformed inputs, writes nothing for them, "
            "accepts the committed record, reports a changed output as stale, and exits with "
            "status 2 and a message when it cannot write its output; --check-all also reports a "
            "listed record that is stale, whose header was altered or that is missing, a design "
            "file or a generated file that the list does not name (the decoy of verification "
            "round 4, issue 4, among them), and a malformed list"
            % (len(cases) + len(arg_cases))), failures


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
