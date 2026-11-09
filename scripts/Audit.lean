import VoltageToBit
import Lean

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

`#audit_axioms` walks **every** declaration defined in a module whose name
starts with `VoltageToBit` (not a hand-picked list), collects the axioms each
one depends on, and fails if any declaration depends on anything outside
`propext`, `Classical.choice`, `Quot.sound`. An unfinished proof (`sorry`)
would show up as `sorryAx`, and `native_decide` as `Lean.ofReduceBool`.

This checks what the Lean kernel accepted in this build. It is not a replay of
the compiled files through an independent checker, and it says nothing about
whether the statements mean what the prose claims.
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Array Name) := #[]
  let mut count : Nat := 0
  let mut thmCount : Nat := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    unless (`VoltageToBit).isPrefixOf modName do continue
    count := count + 1
    if info matches .thmInfo _ then thmCount := thmCount + 1
    let axs ← Lean.collectAxioms name
    for a in axs do
      unless used.contains a do used := used.push a
    let extra := axs.filter fun a => !allowed.contains a
    unless extra.isEmpty do bad := bad.push (name, extra)
  logInfo m!"declarations audited: {count} (of which theorems: {thmCount})"
  logInfo m!"axioms used anywhere: {used.qsort (·.toString < ·.toString)}"
  if bad.isEmpty then
    logInfo "AUDIT OK: no declaration depends on an axiom outside [propext, Classical.choice, Quot.sound]"
  else
    throwError "AUDIT FAILED: {bad}"

#audit_axioms

/-! The headline results, printed individually for the record. -/

open VoltageToBit VoltageToBit.Examples

#print axioms IsTrajectory.safe
#print axioms IsTrajectory.rise
#print axioms IsTrajectory.fall
#print axioms IsTrajectory.decoded
#print axioms exists_solution
#print axioms exists_trajectory
#print axioms exists_trajectory_const
#print axioms IsTrajectory.of_ode
#print axioms IsTrajectory.of_model_error
#print axioms IsTrajectory.rise_of_cert
#print axioms IsTrajectory.fall_of_cert
#print axioms IsTrajectory.rise_at_most
#print axioms Design.Admissible.exists_rise_run
#print axioms Design.Admissible.exists_fall_run
#print axioms chain_restores_low
#print axioms chain_restores_high
#print axioms illustrative_admissible
#print axioms illustrative_guarantee
#print axioms illustrative_exists
#print axioms illustrative_exists_const
#print axioms illustrative_scenario
#print axioms illustrative_riseCert_3
#print axioms badBox_empty
#print axioms early_sampling_counterexample
#print axioms miswired_counterexample
#print axioms noisy_counterexample
#print axioms illustrative_riseCert_rejected
