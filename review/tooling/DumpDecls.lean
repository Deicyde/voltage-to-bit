import VoltageToBit
import Lean

/-!
Workstream E tooling: environment-level inventory of the library.

Prints, for every constant defined in a module whose name starts with
`VoltageToBit`:  name, kind, structural hash of its type, structural hash of
its value (definitions and theorems).  Run against two builds and `diff` the
outputs to see whether both builds contain the same statements.

Also lists everything that could change the *meaning* of later statements
without showing up in an axiom audit: instances, simp lemmas, reducibility
attributes, and non-theorem/non-definition constants.
-/

open Lean Elab Command Meta

elab "#dump_decls" : command => do
  let env ← getEnv
  let mut rows : Array String := #[]
  let mut kinds : Std.HashMap String Nat := {}
  let mut instances : Array Name := #[]
  let mut simps : Array Name := #[]
  let mut reducibles : Array Name := #[]
  let simpThms ← liftTermElabM <| getSimpTheorems
  for (name, info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    unless (`VoltageToBit).isPrefixOf modName do continue
    let kind := match info with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "AXIOM"
      | .opaqueInfo _ => "OPAQUE" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "QUOT"
    kinds := kinds.insert kind (kinds.getD kind 0 + 1)
    let vh := match info.value? (allowOpaque := true) with
      | some v => toString v.hash | none => "-"
    rows := rows.push s!"{name} {kind} {info.type.hash} {vh}"
    if ← liftTermElabM <| isInstance name then instances := instances.push name
    if simpThms.isLemma (.decl name) then simps := simps.push name
    if (← liftCoreM <| getReducibilityStatus name) != .semireducible then
      -- structure projections / matchers / instances are reducible by construction; list them all
      reducibles := reducibles.push name
  for r in rows.qsort (· < ·) do IO.println r
  IO.println s!"## kinds: {kinds.toList}"
  IO.println s!"## instances declared by the library: {instances.qsort (·.toString < ·.toString)}"
  IO.println s!"## simp lemmas declared by the library: {simps.qsort (·.toString < ·.toString)}"
  IO.println s!"## constants with non-default reducibility: {reducibles.qsort (·.toString < ·.toString)}"

#dump_decls
