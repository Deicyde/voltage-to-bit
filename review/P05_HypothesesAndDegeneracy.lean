import VoltageToBit

/-!
# Probe P05 (workstream E): which hypotheses carry weight, and degenerate corners

Small compiled facts about the meaning of the definitions.

* `lawless_outside_safe`: outside the safe domain the inclusion constrains
  nothing; any differentiable function avoiding the safe domain is a
  "trajectory" for every parameter choice and every input.
* `rise_needs_initial_safe`, `rise_needs_inBox`: the hypotheses `v a ∈ Safe`
  and `InBox θ` of `IsTrajectory.rise` cannot be dropped (so they are not
  decorative).
* `trajectory_of_lt`, `trajectory_of_eq`: on an empty or one-point time
  interval every function is a trajectory (harmless: the conclusions are then
  about an empty set of times, see `rise_window_empty`).
* `Admissible.Vlo_neg`, `Admissible.VDDhi_lt_Vhi`, `Admissible.VOH_lt_VDDlo`,
  `Admissible.VOL_pos`: admissibility forces strict inequalities that are only
  stated as weak ones; an admissible record cannot be degenerate in these ways.
* `Iup_not_a_bound_above_VDDlo`, `Idn_not_a_bound_below_zero`: the docstrings
  of `Design.Iup` / `Design.Idn` say the margin is available "whenever
  `u ≤ VIL` and `v ≤ c`" (resp. `VIH ≤ u` and `c ≤ v`). That needs the extra
  hypothesis `c ≤ VDDlo` (resp. `0 ≤ c`) which the theorems do carry.
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.P05

/-! ## The region outside the safe domain is lawless -/

theorem lawless_outside_safe {D : Design} (hC : D.Clo ≤ D.Chi) (θ : Params) (u f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hout : ∀ t, f t ∉ D.Safe) (a b : ℝ) :
    IsTrajectory D θ u f a b :=
  ⟨hf.continuous.continuousOn, fun t _ =>
    ⟨deriv f t, D.Clo, (hf t).hasDerivAt.hasDerivWithinAt, le_rfl, hC,
      fun h => absurd h (hout t)⟩⟩

/-- Without `v a ∈ Safe` the rise guarantee is false: valid-low input, a
"trajectory", never valid-high. -/
theorem rise_needs_initial_safe :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ illustrative.VIL) ∧
      IsTrajectory illustrative nominal u v 0 100 ∧ ∀ t, v t < illustrative.VOH := by
  refine ⟨fun _ => 0, fun _ => -1, fun _ => by norm_num [illustrative], ?_,
    fun _ => by norm_num [illustrative]⟩
  refine lawless_outside_safe (by norm_num [illustrative]) nominal _ _ (differentiable_const _)
    (fun t h => ?_) 0 100
  have h1 : illustrative.Vlo ≤ (-1 : ℝ) := h.1
  norm_num [illustrative] at h1

/-- Without `InBox θ` the rise guarantee is false: with `k_p = 0` (no pull-up)
the output rests at 0 V under a valid-low input, starting inside the safe
domain. -/
theorem rise_needs_inBox :
    ∃ (θ : Params) (u v : ℝ → ℝ), (∀ t, u t ≤ illustrative.VIL) ∧ v 0 ∈ illustrative.Safe ∧
      IsTrajectory illustrative θ u v 0 100 ∧ ∀ t, v t < illustrative.VOH := by
  refine ⟨⟨1.8, 200, 0, 0.5, 0.5⟩, fun _ => 0, fun _ => 0, fun _ => by norm_num [illustrative],
    by norm_num [Design.Safe, illustrative],
    ⟨continuousOn_const, fun t _ => ⟨0, 5, hasDerivWithinAt_const t _ _, ?_, ?_, fun _ => ?_⟩⟩,
    fun _ => by norm_num [illustrative]⟩
  · norm_num [illustrative]
  · norm_num [illustrative]
  · norm_num [illustrative, Inet, Ip, In, psq_eq_ite]

/-! ## Degenerate time intervals -/

theorem trajectory_of_lt (D : Design) (θ : Params) (u v : ℝ → ℝ) {a b : ℝ} (h : b < a) :
    IsTrajectory D θ u v a b :=
  ⟨by rw [Icc_eq_empty (not_le.mpr h)]; exact continuousOn_empty v,
    fun t ht => absurd (lt_of_le_of_lt ht.1 ht.2) (not_lt.mpr h.le)⟩

theorem trajectory_of_eq (D : Design) (θ : Params) (u v : ℝ → ℝ) (a : ℝ) :
    IsTrajectory D θ u v a a :=
  ⟨by rw [Icc_self]; exact continuousOn_singleton v a,
    fun t ht => absurd (lt_of_le_of_lt ht.1 ht.2) (lt_irrefl a)⟩

/-- If the valid-input window is shorter than the deadline, the conclusion of
`IsTrajectory.rise` is about an empty set of times. -/
theorem rise_window_empty {D : Design} {s e : ℝ} (h : e < s + D.tauUp) :
    {t | t ∈ Icc s e ∧ s + D.tauUp ≤ t} = ∅ := by
  ext t
  simp only [mem_ofPred_eq, mem_Icc, mem_empty_iff_false, iff_false, not_and, not_le]
  intro ht
  linarith [ht.2]

/-! ## Strictness forced by admissibility -/

namespace Admissible

variable {D : Design}

theorem Vlo_neg (hD : D.Admissible) : D.Vlo < 0 := by
  rcases lt_or_eq_of_le hD.Vlo_le with h | h
  · exact h
  · exfalso
    have h1 := hD.loN
    unfold Design.RloN at h1
    rw [h, sub_zero, sub_self, mul_zero] at h1
    linarith [hD.eps_nonneg]

theorem VDDhi_lt_Vhi (hD : D.Admissible) : D.VDDhi < D.Vhi := by
  rcases lt_or_eq_of_le hD.Vhi_ge with h | h
  · exact h
  · exfalso
    have h1 := hD.hiP
    unfold Design.RhiP at h1
    rw [← h, sub_self, add_zero, sub_self, mul_zero] at h1
    linarith [hD.eps_nonneg]

theorem VOH_lt_VDDlo (hD : D.Admissible) : D.VOH < D.VDDlo := by
  rcases lt_or_eq_of_le hD.VOH_le with h | h
  · exact h
  · exfalso
    have h1 := hD.up
    unfold Design.Iup at h1
    rw [h, sub_self, mul_zero, zero_sub] at h1
    have h2 : 0 ≤ D.knhi / 2 * psq (D.VIL - D.Vtnlo) :=
      mul_nonneg (by linarith [hD.kn_pos, hD.kn_le]) (psq_nonneg _)
    linarith [hD.eps_nonneg]

theorem VOL_pos (hD : D.Admissible) : 0 < D.VOL := by
  rcases lt_or_eq_of_le hD.VOL_nonneg with h | h
  · exact h
  · exfalso
    have h1 := hD.dn
    unfold Design.Idn at h1
    rw [← h, sub_zero, sub_self, mul_zero, zero_sub] at h1
    have h2 : 0 ≤ D.kphi / 2 * psq (D.VDDhi - D.VIH - D.Vtplo) :=
      mul_nonneg (by linarith [hD.kp_pos, hD.kp_le]) (psq_nonneg _)
    linarith [hD.eps_nonneg]

end Admissible

/-! ## The side conditions of the two margin theorems are needed -/

/-- For `c > VDDlo` the number `Iup c` is NOT a lower bound of the device
current, although `u ≤ VIL` and `v ≤ c`. -/
theorem Iup_not_a_bound_above_VDDlo :
    ∃ (θ : Params) (u v c : ℝ), illustrative.InBox θ ∧ u ≤ illustrative.VIL ∧ v ≤ c ∧
      Inet θ u v < illustrative.Iup c := by
  refine ⟨⟨1.62, 240, 120, 0.45, 0.60⟩, 0.40, 1.7, 1.7, ?_, ?_, le_rfl, ?_⟩
  · constructor <;> norm_num [illustrative]
  · norm_num [illustrative]
  · norm_num [illustrative, Design.Iup, Inet, Ip, In, psq_eq_ite]

/-- For `c < 0` the number `Idn c` is NOT a lower bound of the discharge
current, although `VIH ≤ u` and `c ≤ v`. -/
theorem Idn_not_a_bound_below_zero :
    ∃ (θ : Params) (u v c : ℝ), illustrative.InBox θ ∧ illustrative.VIH ≤ u ∧ c ≤ v ∧
      -illustrative.Idn c < Inet θ u v := by
  refine ⟨⟨1.98, 240, 120, 0.60, 0.45⟩, 1.25, -0.1, -0.1, ?_, ?_, le_rfl, ?_⟩
  · constructor <;> norm_num [illustrative]
  · norm_num [illustrative]
  · norm_num [illustrative, Design.Idn, Inet, Ip, In, psq_eq_ite]

end Review.P05

#print axioms Review.P05.lawless_outside_safe
#print axioms Review.P05.rise_needs_initial_safe
#print axioms Review.P05.rise_needs_inBox
#print axioms Review.P05.Admissible.Vlo_neg
#print axioms Review.P05.Admissible.VDDhi_lt_Vhi
#print axioms Review.P05.Admissible.VOH_lt_VDDlo
#print axioms Review.P05.Admissible.VOL_pos
#print axioms Review.P05.Iup_not_a_bound_above_VDDlo
#print axioms Review.P05.Idn_not_a_bound_below_zero
