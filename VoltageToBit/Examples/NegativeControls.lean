import VoltageToBit.Examples.Illustrative
import VoltageToBit.Proofs.Contamination

/-!
# Negative controls

Each control changes one thing about the illustrative instance and shows that
the guarantee is then either *rejected* (a numeric condition fails) or
*refuted* (an explicit trajectory violates the conclusion). Failing a
sufficient condition does not by itself show that a circuit fails, so the
controls exhibit trajectories wherever possible.

1. `badBox_*`: inconsistent parameter bounds. The record is rejected, and the
   box is shown to be empty (the guarantee would have been vacuous).
2. `illustrative_no_early_high`, `early_sampling_counterexample`: insufficient
   observation time. No trajectory starting valid-low can be valid-high within
   38 ps; a claimed deadline that short is false.
3. `miswired_counterexample`: the two transistors exchanged. The output can sit
   at 0.3 V forever while the input is valid-low.
4. `noisy_*`: a disturbance allowance of 10.76 µA, just above the pull-up
   margin of 10.476 µA. The record is rejected, and a trajectory stuck at
   1.34 V < `VOH` exists.
5. `illustrative_riseCert_rejected`: a certificate claiming a deadline its
   levels do not support is rejected.
-/

namespace VoltageToBit.Examples

open Set

/-! ## 1. Inconsistent parameter bounds -/

/-- The illustrative record with the NMOS transconductance range inverted
(lower bound 300 above upper bound 240). -/
noncomputable def badBox : Design := { illustrative with knlo := 300 }

theorem badBox_not_admissible : ¬ badBox.Admissible := fun h => by
  have h1 := h.kn_le
  norm_num [badBox, illustrative] at h1

/-- The inverted box contains no parameter choice at all, so any statement
quantified over it would be vacuously true. `Admissible` rules this out. -/
theorem badBox_empty : ∀ θ : Params, ¬ badBox.InBox θ := fun θ h => by
  have h1 := h.kn_ge
  have h2 := h.kn_le
  norm_num [badBox, illustrative] at h1 h2
  linarith

/-! ## 2. Insufficient observation time -/

/-- With the input in `[0, 0.40]` V and the output starting valid-low, the
output is still below `VOH = 1.35` V at every time up to 38 ps later. -/
theorem illustrative_no_early_high (u v : ℝ → ℝ)
    (a b : ℝ) (h : IsTrajectory illustrative u v a b) (h0 : v a ∈ illustrative.Safe)
    (s e : ℝ) (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, 0 ≤ u t ∧ u t ≤ 0.40)
    (hvs : v s ≤ 0.25) :
    ∀ t ∈ Icc s e, t ≤ s + 0.038 → v t < 1.35 := by
  intro t ht htime
  have hbound := h.rise_at_most illustrative_admissible h0 hs he hu hvs t ht
  have hslope : (illustrative.IchargeMax 0 0.40 + illustrative.eps) / illustrative.Clo
      = 28.5508 := by
    norm_num [Design.IchargeMax, illustrative, psq_eq_ite]
  rw [hslope] at hbound
  have : t - s ≤ 0.038 := by linarith
  nlinarith [ht.1]

/-- Largest rising slew of the illustrative output for inputs in `[0, 0.40]` V:
28.5508 V/ns. -/
theorem illustrative_max_rise_slew :
    (illustrative.IchargeMax 0 0.40 + illustrative.eps) / illustrative.Clo = 28.5508 := by
  norm_num [Design.IchargeMax, illustrative, psq_eq_ite]

/-- Largest falling slew of the illustrative output for inputs in
`[1.25, 1.98]` V: 58.3144 V/ns. -/
theorem illustrative_max_fall_slew :
    (illustrative.IdischargeMax 1.25 1.98 + illustrative.eps) / illustrative.Clo
      = 58.3144 := by
  norm_num [Design.IdischargeMax, illustrative, psq_eq_ite]

/-- A claimed rise deadline of 38 ps is false: there is a trajectory with a
valid-low input from time 0 and a valid-low initial output that is not
valid-high at `t = 0.038` ns. -/
theorem early_sampling_counterexample :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧ v 0 ≤ 0.25 ∧
      IsTrajectory illustrative u v 0 10 ∧ v 0.038 < 1.35 := by
  obtain ⟨v, hv0, htraj⟩ := illustrative_exists_const nominal nominal_inBox 5 (by norm_num)
    (fun _ => 0.2) (fun _ => 0) continuous_const continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) 0.25 (by norm_num)
  refine ⟨fun _ => 0.2, v, fun t => by norm_num, hv0.le, htraj, ?_⟩
  have h0 : v 0 ∈ illustrative.Safe := by
    rw [hv0]; norm_num [Design.Safe, illustrative]
  exact illustrative_no_early_high _ v 0 10 htraj h0 0 10 le_rfl le_rfl
    (fun t _ => by norm_num) hv0.le 0.038 (by norm_num) (by norm_num)

/-! ## 3. Miswired transistors -/

/-- Net current into the output node when the transistors are exchanged:
the NMOS pulls up (drain at the supply, source at the output) and the PMOS
pulls down (source at the output, drain at ground), both gates on the input. -/
noncomputable def InetSwapped (θ : Params) (u v : ℝ) : ℝ :=
  θ.kn / 2 * (psq (u - v - θ.Vtn) - psq (u - θ.VDD - θ.Vtn))
    - θ.kp / 2 * (psq (v - u - θ.Vtp) - psq (0 - u - θ.Vtp))

/-- The miswired network is not an inverter: with the input held at 0 V
(valid-low) the output can rest at 0.3 V forever. The disturbance is zero and
the same capacitance and error bounds as the illustrative instance are used. -/
theorem miswired_counterexample (T : ℝ) :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧ v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧
      ContinuousOn v (Icc 0 T) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
        (5 : ℝ) ≤ c ∧ c ≤ 20 ∧ |c * v' - InetSwapped nominal (u t) (v t)| ≤ 2) ∧
      ∀ t, v t < 1.35 := by
  refine ⟨fun _ => 0, fun _ => 0.3, fun t => by norm_num, by norm_num, continuousOn_const,
    fun t _ => ⟨0, 5, hasDerivWithinAt_const t _ _, le_rfl, by norm_num, ?_⟩,
    fun t => by norm_num⟩
  norm_num [InetSwapped, nominal, psq_eq_ite]

/-! ## 4. A disturbance allowance that destroys the pull-up margin -/

/-- The illustrative record with the disturbance allowance raised from 2 µA to
10.76 µA, just above the pull-up margin `Iup VOH = 10.476` µA. -/
noncomputable def noisy : Design := { illustrative with eps := 10.76 }

/-- The weak pull-up corner of the box: lowest supply, weakest PMOS with the
largest threshold, strongest NMOS with the smallest threshold. -/
def weakCorner : Params := ⟨1.62, 240, 80, 0.45, 0.60⟩

theorem weakCorner_inBox : noisy.InBox weakCorner := by
  constructor <;> norm_num [noisy, illustrative, weakCorner]

theorem noisy_not_admissible : ¬ noisy.Admissible := fun h => by
  have h1 := h.up
  norm_num [noisy, illustrative, Design.Iup, psq_eq_ite] at h1

/-- With the larger allowance the guarantee is false, not merely unproved:
at the weak corner, with the input held valid-low at 0.40 V, the output can
rest at 1.34 V, below `VOH = 1.35` V, forever. -/
theorem noisy_counterexample (T : ℝ) :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ noisy.VIL) ∧ v 0 ∈ noisy.Safe ∧
      IsTrajectory noisy u v 0 T ∧ ∀ t, v t < noisy.VOH := by
  refine ⟨fun _ => 0.40, fun _ => 1.34, fun t => by norm_num [noisy, illustrative],
    by norm_num [Design.Safe, noisy, illustrative],
    ⟨continuousOn_const, fun t _ => ⟨0, 5, hasDerivWithinAt_const t _ _, ?_, ?_,
      fun _ => ⟨weakCorner, weakCorner_inBox, ?_⟩⟩⟩,
    fun t => by norm_num [noisy, illustrative]⟩
  · norm_num [noisy, illustrative]
  · norm_num [noisy, illustrative]
  · norm_num [noisy, illustrative, weakCorner, Inet, Ip, In, psq_eq_ite, abs_le]

/-! ## 5. An unjustified certificate is rejected -/

/-- The three-level certificate supports a 2.34 ns deadline
(`illustrative_riseCert_3`) but not a 2.0 ns one. -/
theorem illustrative_riseCert_rejected : ¬ illustrative.ValidRiseCert 1.0 [1.2, 1.35] 2.0 := by
  rintro ⟨-, -, hτ⟩
  norm_num [riseTime, Design.upSegs, Design.Iup, illustrative, psq_eq_ite] at hτ

end VoltageToBit.Examples
