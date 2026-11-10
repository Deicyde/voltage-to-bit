import VoltageToBit
import Lean

/-!
# Axiom audit and census of the library

Run with `lake env lean scripts/Audit.lean` after `lake build`
(`scripts/check.sh` does both and compares the result with the sources).

`#audit_library` looks at the environment obtained by importing the root
module `VoltageToBit`, and at **every** declaration defined in a module whose
name starts with `VoltageToBit` (not a hand-picked list). It

* lists those modules with the number of declarations each one contributes
  (this is the import closure of the root module; `scripts/check.sh` compares
  the list with the `.lean` files on disk, so that a file nobody imports is
  noticed);
* collects the axioms each declaration depends on and fails if any declaration
  depends on anything outside `propext`, `Classical.choice`, `Quot.sound`
  (an unfinished proof shows up as `sorryAx`, `native_decide` as
  `Lean.ofReduceBool` or `Lean.trustCompiler`, a declared axiom as itself);
* prints every theorem of the library that has a name of its own, with the
  axioms it depends on (all of them, not a selection, so the list cannot go
  stale when a theorem is added or renamed);
* fails if the library declares an axiom, an `opaque` constant, an `unsafe`
  constant, or anything registered as an instance or as a simp lemma other
  than what Lean generates for every structure.

If the environment variable `VTB_AUDIT_LISTS` names a directory, the module
names and the names of the declarations are also written there, for the
kernel replay steps of `scripts/check.sh`.

This reads what is stored in the compiled files. It does not re-check
anything: a declaration that was added with the kernel check switched off
looks the same from here as any other (see `review/tooling/AuditGapDemo.lean`).
Re-checking is the job of the replay steps. And it says nothing about whether
the statements mean what the prose claims.
-/

open Lean Elab Command Meta

/-- The components of a name as JSON: strings and numbers. -/
def nameComponents : Name → List Json
  | .anonymous => []
  | .str p s => nameComponents p ++ [toJson s]
  | .num p n => nameComponents p ++ [toJson n]

/-- Is `s` the last component of `n`? -/
def lastComponentIs (n : Name) (s : String) : Bool :=
  match n with
  | .str _ t => t == s
  | _ => false

/-- Is `n` a definition that the kernel checked as an ordinary (safe) one? -/
def isSafeDefinition (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo d) => d.safety == .safe
  | _ => false

elab "#audit_library" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let isProject (m : Name) : Bool := (`VoltageToBit).isPrefixOf m
  -- modules of the library in this environment
  let mut perModule : Std.HashMap Name Nat := {}
  for m in env.header.moduleNames do
    if isProject m then perModule := perModule.insert m 0
  let simpThms ← liftTermElabM getSimpTheorems
  let mut bad : Array (Name × Array Name) := #[]
  let mut count : Nat := 0
  let mut thmCount : Nat := 0
  let mut kinds : Std.HashMap String Nat := {}
  let mut used : Array Name := #[]
  let mut checkable : Array Name := #[]
  let mut partials : Array Name := #[]
  let mut refused : Array String := #[]
  let mut theorems : Array String := #[]
  for (name, info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    unless isProject modName do continue
    count := count + 1
    perModule := perModule.insert modName (perModule.getD modName 0 + 1)
    if info matches .thmInfo _ then thmCount := thmCount + 1
    let kind := match info with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive type" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .quotInfo _ => "quotient primitive"
    kinds := kinds.insert kind (kinds.getD kind 0 + 1)
    if kind == "axiom" || kind == "opaque" || kind == "quotient primitive" then
      refused := refused.push s!"{name} is declared as: {kind}"
    -- For a definition by recursion `f` Lean also stores an auxiliary `f._unsafe_rec`,
    -- marked `partial`, which exists for the compiler. Lean's kernel refuses a safe
    -- definition or a theorem that refers to a `partial` or `unsafe` constant ("safe
    -- declaration must not contain partial declaration", "it uses unsafe declaration"),
    -- and `leanchecker` leaves such constants out of its replay. So an auxiliary of
    -- this form belonging to a safe definition is listed, by name, as not re-checked;
    -- anything else that is `unsafe` or `partial` is refused here.
    if info.isUnsafe then
      refused := refused.push s!"{name} is unsafe"
    else if info.isPartial then
      if lastComponentIs name "_unsafe_rec" && isSafeDefinition env name.getPrefix then
        partials := partials.push name
      else refused := refused.push s!"{name} is partial"
    else
      checkable := checkable.push name
    if ← liftTermElabM <| isInstance name then
      unless lastComponentIs name "_sizeOf_inst" do
        refused := refused.push s!"{name} is registered as an instance"
    if simpThms.isLemma (.decl name) then
      unless lastComponentIs name "injEq" || lastComponentIs name "sizeOf_spec" do
        refused := refused.push s!"{name} is registered as a simp lemma"
    let axs ← Lean.collectAxioms name
    for a in axs do
      unless used.contains a do used := used.push a
    let extra := axs.filter fun a => !allowed.contains a
    unless extra.isEmpty do bad := bad.push (name, extra)
    -- auxiliary and private declarations (`_proof_1`, `match_1`, `_private...`) are audited
    -- like the others but not listed
    if (info matches .thmInfo _) && !name.isInternal then
      let sorted := (axs.map (·.toString)).qsort (· < ·)
      let shown := if sorted.isEmpty then "no axioms" else ", ".intercalate sorted.toList
      theorems := theorems.push s!"{name}: {shown}"
  let modules := perModule.toArray.qsort (·.1.toString < ·.1.toString)
  checkable := checkable.qsort (·.toString < ·.toString)
  partials := partials.qsort (·.toString < ·.toString)
  if let some dir ← IO.getEnv "VTB_AUDIT_LISTS" then
    let dir : System.FilePath := dir
    let lines (xs : Array String) : String := String.join (xs.toList.map (· ++ "\n"))
    IO.FS.writeFile (dir / "modules.txt") (lines (modules.map (·.1.toString)))
    IO.FS.writeFile (dir / "constants.txt") (lines (checkable.map (·.toString (escape := true))))
    IO.FS.writeFile (dir / "constants.jsonl")
      (lines (checkable.map fun n => (Json.arr (nameComponents n).toArray).compress))
    IO.FS.writeFile (dir / "skipped.txt") (lines (partials.map (·.toString)))
  let moduleLines := modules.toList.map fun (m, k) => s!"\n  {m}: {k} declarations"
  logInfo m!"project modules in the audited environment: {modules.size}\
    {String.join moduleLines}"
  -- `map₁` holds what was imported; the few declarations of this script are not in it
  let total : Nat := env.constants.map₁.size
  let compilerOnly : Nat := env.constants.map₁.fold
    (fun n _ c => if c.isUnsafe || c.isPartial then n + 1 else n) 0
  logInfo m!"imported environment: {env.header.moduleNames.size} modules, {total} declarations"
  logInfo m!"of these, marked unsafe or partial (they exist for the compiler; the replay tools \
    leave them out, and the kernel lets no safe definition or theorem refer to them): {compilerOnly}"
  logInfo m!"declarations audited: {count} (of which theorems: {thmCount})"
  let kindLines := (kinds.toArray.qsort (·.1 < ·.1)).toList.map fun (k, v) => s!"{k}: {v}"
  logInfo m!"kinds: {", ".intercalate kindLines}"
  logInfo m!"declarations that the replay steps re-check: {checkable.size}; compiler auxiliaries \
    marked partial, which they leave out and to which the kernel lets no safe definition or \
    theorem refer: {partials.size}\
    {String.join (partials.toList.map fun n => s!"\n  {n}")}"
  logInfo m!"axioms used anywhere: {used.qsort (·.toString < ·.toString)}"
  unless refused.isEmpty do
    throwError "AUDIT FAILED: the library contains declarations of a kind it must not contain:\
      {String.join (refused.toList.map fun s => "\n  " ++ s)}"
  unless bad.isEmpty do
    throwError "AUDIT FAILED: {bad}"
  logInfo "AUDIT OK: no declaration depends on an axiom outside [propext, Classical.choice, Quot.sound]"
  theorems := theorems.qsort (· < ·)
  logInfo m!"theorems with a name of their own, and the axioms each one depends on \
    ({theorems.size}):{String.join (theorems.toList.map fun t => "\n  " ++ t)}"

#audit_library
