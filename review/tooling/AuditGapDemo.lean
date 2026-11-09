import Lean

/-!
Workstream E tooling demo: what an axiom audit plus a token grep cannot see.

This file is NOT part of the library and imports nothing from it. It adds a
"theorem" of type `False` to the environment while the kernel check is switched
off by an option. Afterwards:

* `#print axioms` reports no axioms at all for it (so `scripts/Audit.lean`
  would print AUDIT OK for a library containing such a declaration);
* the file contains none of the tokens that `scripts/check.sh` greps for
  (the five proof-escape keywords, a leading axiom declaration, extern attributes);
* a kernel replay of the compiled file (`leanchecker`) rejects it.

Purpose: to show that step 4 of `scripts/check.sh` does not by itself
establish "the Lean kernel accepted every declaration in this build".
-/

open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (.thmDecl {
  name := `AuditGapDemo.bad, levelParams := [], type := mkConst ``False,
  value := mkConst ``True.intro }))

theorem AuditGapDemo.oops : False := AuditGapDemo.bad

#print axioms AuditGapDemo.bad
#print axioms AuditGapDemo.oops
