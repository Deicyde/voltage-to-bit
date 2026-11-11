import VoltageToBit.Examples.Illustrative
import VoltageToBit.Proofs.Chain
import VoltageToBit.Proofs.Concat

/-!
# Two illustrative stages in series: an actual run

`Proofs/Chain.lean` proves that two stages in series restore a bit
(`chain_low`, `chain_high`, `chain_restores_low`, `chain_restores_high`). These
are implications about a pair of trajectories in which the input of the second
stage is the output of the first; that file has no existence statement. The
existence theorem of the library cannot be applied to the second stage as it
stands: it asks for an input that is continuous on all of ℝ, and the output of
a first stage is only known to be continuous on the time interval. This file
supplies the missing witness for the illustrative record.

* `exists_second_stage`: for any input that is continuous on `[0, 10]`, in
  particular for the output of a first-stage trajectory, there is a
  second-stage trajectory on `[0, 10]`, from any initial state in the safe
  domain.
* `chain_witness`: an actual two-stage run on `[0, 10]` ns. The first input is
  held at 0 V (valid-low) and both outputs start at 1.0 V, which decodes to
  *undefined* (`illustrative_initial_undefined`). The first output is
  valid-high throughout `[3.43, 10]` ns and the second output is valid-low
  throughout `[6, 10]` ns. The last fact is obtained from `chain_restores_low`,
  so the hypotheses of that corollary can be met and its conclusion is about a
  window of positive length.
* `chain_witness_high`: the mirror image, for `chain_restores_high`. The first
  input is held at 1.8 V (valid-high); the first output is valid-low throughout
  `[2.57, 10]` ns and the second output is valid-high throughout `[6, 10]` ns.

In both runs each stage is built with nominal parameters, a capacitance of
10 fF and zero disturbance. The statements only record that both outputs are
trajectories of the illustrative record.

Modelling caveat. Such a run is a run of **two ideal one-node stages**, exactly
as in `Proofs/Chain.lean`. Each stage is the one-node model: its only state is
its own output voltage, and the other stage enters only as the input function
of its device currents. The gate capacitance that the second stage presents to
the first output, and the current that a moving first output injects into the
second output through the second stage's gate-drain capacitance, are not
modelled. They are covered only if the capacitance range and the 2 µA
allowance of the record contain them. That is an assumption about the
environment which nothing here proves, and `docs/model.md`, section 7.4,
argues that under its Budget A (an environment consistent with the 2 µA
allowance) the two-stage corollary has no physical reading. The witnesses show
that the corollary is not vacuous as mathematics. They are not a verified
two-gate circuit.

Provenance. `chain_witness` was contributed by workstream E's review probe
`review/D04_AtSupply_Chain_Reverse.lean`, part B (finding E2-03 of
`docs/adversarial-review.md`), and ported into the library. Added in the port:
`exists_second_stage` as a lemma of its own, the conjunct about the first
output, and the mirror image `chain_witness_high`.
-/

namespace VoltageToBit.Examples

open Set

/-- **A second stage can be driven by the output of a first one.** For an input
`v₁` that is continuous on `[0, 10]`, in particular for the output of a
first-stage trajectory on `[0, 10]`, there is a trajectory of the illustrative
record on `[0, 10]` whose input is `v₁`, from any initial state in the safe
domain. (The proof builds it with nominal parameters, capacitance 10 fF and
zero disturbance; the statement does not name these data.)

The existence theorem wants an input that is continuous on all of ℝ; `v₁` is
only assumed continuous on `[0, 10]`. So the solution is built for the input
`v₁ ∘ clamp 0 10`, which is continuous everywhere and equals `v₁` on `[0, 10]`,
and a trajectory only depends on the input on `[0, 10)`. -/
theorem exists_second_stage {v₁ : ℝ → ℝ} (hv₁ : ContinuousOn v₁ (Icc 0 10))
    (v₀ : ℝ) (hv₀ : v₀ ∈ Icc (-0.10 : ℝ) 2.08) :
    ∃ v₂ : ℝ → ℝ, v₂ 0 = v₀ ∧ IsTrajectory illustrative v₁ v₂ 0 10 := by
  -- a globally continuous copy of the first output, to feed the existence theorem
  have hcl : Continuous (clamp 0 10) := by unfold clamp; fun_prop
  have hcu : Continuous (fun t => v₁ (clamp 0 10 t)) :=
    hv₁.comp_continuous hcl (fun t => clamp_mem (by norm_num) t)
  obtain ⟨v₂, hv₂0, h₂⟩ := illustrative_exists_const nominal nominal_inBox 10 (by norm_num)
    (fun t => v₁ (clamp 0 10 t)) (fun _ => 0) hcu continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) v₀ hv₀
  exact ⟨v₂, hv₂0, h₂.congr_input (fun t ht => by
    show v₁ (clamp 0 10 t) = v₁ t
    rw [clamp_of_mem ⟨ht.1, ht.2.le⟩])⟩

/-- **A two-stage run that restores a low bit.** There are an input `u` and
outputs `v₁`, `v₂` on `[0, 10]` ns such that: `u` is valid-low at all times;
`v₁` is a trajectory of the illustrative record for the input `u`; `v₂` is a
trajectory of the illustrative record for the input `v₁`; both outputs start at
1.0 V; the first output is valid-high on `[3.43, 10]` ns; and the second output
is valid-low on `[6, 10]` ns.

This is a run of two ideal one-node stages (see the modelling caveat in the
header of this file). -/
theorem chain_witness :
    ∃ u v₁ v₂ : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧
      IsTrajectory illustrative u v₁ 0 10 ∧ IsTrajectory illustrative v₁ v₂ 0 10 ∧
      v₁ 0 = 1 ∧ v₂ 0 = 1 ∧
      (∀ t ∈ Icc (3.43 : ℝ) 10, 1.35 ≤ v₁ t) ∧ ∀ t ∈ Icc (6 : ℝ) 10, v₂ t ≤ 0.25 := by
  have hadm := illustrative_admissible
  obtain ⟨v₁, hv₁0, h₁⟩ := illustrative_exists_const nominal nominal_inBox 10 (by norm_num)
    (fun _ => 0) (fun _ => 0) continuous_const continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) 1 (by norm_num)
  obtain ⟨v₂, hv₂0, h₂⟩ := exists_second_stage h₁.cont 1 (by norm_num)
  have hs : (1 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  refine ⟨fun _ => 0, v₁, v₂, fun _ => by norm_num, h₁, h₂, hv₁0, hv₂0,
    fun t ht => ?_, fun t ht => ?_⟩
  · have := h₁.rise hadm (by rw [hv₁0]; exact hs) (s := 0) (e := 10) le_rfl le_rfl
      (fun _ _ => by norm_num [illustrative]) t ⟨by linarith [ht.1], ht.2⟩
      (by linarith [ht.1, illustrative_tauUp_le])
    simpa [illustrative] using this
  · have := chain_restores_low hadm h₁ h₂ (by rw [hv₁0]; exact hs) (by rw [hv₂0]; exact hs)
      (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) t
      ⟨by linarith [ht.1], ht.2⟩
      (by linarith [ht.1, illustrative_tauUp_le, illustrative_tauDn_le])
    simpa [illustrative] using this

/-- **A two-stage run that restores a high bit.** Mirror image of
`chain_witness`: `u` is valid-high at all times; both outputs start at 1.0 V;
the first output is valid-low on `[2.57, 10]` ns; and the second output is
valid-high on `[6, 10]` ns.

This is a run of two ideal one-node stages (see the modelling caveat in the
header of this file). -/
theorem chain_witness_high :
    ∃ u v₁ v₂ : ℝ → ℝ, (∀ t, 1.25 ≤ u t) ∧
      IsTrajectory illustrative u v₁ 0 10 ∧ IsTrajectory illustrative v₁ v₂ 0 10 ∧
      v₁ 0 = 1 ∧ v₂ 0 = 1 ∧
      (∀ t ∈ Icc (2.57 : ℝ) 10, v₁ t ≤ 0.25) ∧ ∀ t ∈ Icc (6 : ℝ) 10, 1.35 ≤ v₂ t := by
  have hadm := illustrative_admissible
  obtain ⟨v₁, hv₁0, h₁⟩ := illustrative_exists_const nominal nominal_inBox 10 (by norm_num)
    (fun _ => 1.8) (fun _ => 0) continuous_const continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) 1 (by norm_num)
  obtain ⟨v₂, hv₂0, h₂⟩ := exists_second_stage h₁.cont 1 (by norm_num)
  have hs : (1 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  refine ⟨fun _ => 1.8, v₁, v₂, fun _ => by norm_num, h₁, h₂, hv₁0, hv₂0,
    fun t ht => ?_, fun t ht => ?_⟩
  · have := h₁.fall hadm (by rw [hv₁0]; exact hs) (s := 0) (e := 10) le_rfl le_rfl
      (fun _ _ => by norm_num [illustrative]) t ⟨by linarith [ht.1], ht.2⟩
      (by linarith [ht.1, illustrative_tauDn_le])
    simpa [illustrative] using this
  · have := chain_restores_high hadm h₁ h₂ (by rw [hv₁0]; exact hs) (by rw [hv₂0]; exact hs)
      (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) t
      ⟨by linarith [ht.1], ht.2⟩
      (by linarith [ht.1, illustrative_tauUp_le, illustrative_tauDn_le])
    simpa [illustrative] using this

end VoltageToBit.Examples
