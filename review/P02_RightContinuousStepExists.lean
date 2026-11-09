import VoltageToBit

/-!
# Probe P02 (workstream E): the right-continuous twin of the step input DOES have trajectories

Companion of `P01_JumpInputVacuity.lean`. The input `uStepR` (high for `t < 4`,
low for `t ≥ 4`) differs from `uStepL` of P01 at the single instant `t = 4`.
Here trajectories exist from every initial state in the safe domain
(`stepR_has_trajectory`), by gluing two solutions of the library's existence
theorem. So the emptiness shown in P01 is caused only by the value the input
takes *at* the jump instant.

The library itself proves existence only for continuous inputs
(`exists_solution`). The two general lemmas below
(`IsTrajectory.congr_input`, `IsTrajectory.concat`) are what is needed to
extend existence to right-continuous piecewise-continuous inputs; they are
offered as a possible repair, not as part of the reviewed development.
-/

open Set Filter Topology
open VoltageToBit VoltageToBit.Examples

namespace Review.P02

/-- A trajectory depends on the input only through its values on `[a, b)`. -/
theorem IsTrajectory.congr_input {D : Design} {θ : Params} {u u' v : ℝ → ℝ} {a b : ℝ}
    (h : IsTrajectory D θ u v a b) (hu : ∀ t ∈ Ico a b, u t = u' t) :
    IsTrajectory D θ u' v a b where
  cont := h.cont
  incl := fun t ht => by
    obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h.incl t ht
    exact ⟨v', c, hd, hc1, hc2, by rw [← hu t ht]; exact hb⟩

/-- **Concatenation.** Two trajectories for the same input that agree at the
junction glue to a trajectory on the union of the intervals. -/
theorem IsTrajectory.concat {D : Design} {θ : Params} {u v₁ v₂ : ℝ → ℝ} {a m b : ℝ}
    (h₁ : IsTrajectory D θ u v₁ a m) (h₂ : IsTrajectory D θ u v₂ m b)
    (ham : a ≤ m) (hmb : m ≤ b) (hjoin : v₁ m = v₂ m) :
    IsTrajectory D θ u (fun t => if t < m then v₁ t else v₂ t) a b where
  cont := by
    have e1 : EqOn (fun t => if t < m then v₁ t else v₂ t) v₁ (Icc a m) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · simp [h, hjoin]
      · simp [h]
    have e2 : EqOn (fun t => if t < m then v₁ t else v₂ t) v₂ (Icc m b) := by
      intro t ht
      simp [not_lt.mpr ht.1]
    have c1 := h₁.cont.congr e1
    have c2 := h₂.cont.congr e2
    have := c1.union_of_isClosed c2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc ham hmb] at this
  incl := fun t ht => by
    rcases lt_or_ge t m with htm | htm
    · obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h₁.incl t ⟨ht.1, htm⟩
      refine ⟨v', c, ?_, hc1, hc2, by simpa [htm] using hb⟩
      have hev : (fun s => if s < m then v₁ s else v₂ s) =ᶠ[𝓝[Ici t] t] v₁ := by
        have : Iio m ∈ 𝓝[Ici t] t := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htm)
        filter_upwards [this] with s hs
        simp [mem_Iio.mp hs]
      exact hd.congr_of_eventuallyEq hev (by simp [htm])
    · obtain ⟨v', c, hd, hc1, hc2, hb⟩ := h₂.incl t ⟨htm, ht.2⟩
      refine ⟨v', c, ?_, hc1, hc2, by simpa [not_lt.mpr htm] using hb⟩
      refine hd.congr (fun s hs => ?_) (by simp [not_lt.mpr htm])
      have : ¬ s < m := not_lt.mpr (le_trans htm hs)
      simp [this]

/-- High until `t = 4` **exclusive**, low from `t = 4` on. -/
noncomputable def uStepR (t : ℝ) : ℝ := if t < 4 then 1.8 else 0

/-- **Trajectories exist for the right-continuous step**, from every initial
state in the safe domain (constant capacitance 10 fF, zero disturbance). -/
theorem stepR_has_trajectory (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧ IsTrajectory illustrative nominal uStepR v 0 10 := by
  have hadm := illustrative_admissible
  have hθ := nominal_inBox
  have hC1 : illustrative.Clo ≤ (10 : ℝ) := by norm_num [illustrative]
  have hC2 : (10 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hw : ∀ (a b : ℝ), ∀ t ∈ Icc a b, |(fun _ : ℝ => (0 : ℝ)) t| ≤ illustrative.eps :=
    fun _ _ t _ => by simpa using hadm.eps_nonneg
  -- first piece: input high on [0, 4]
  obtain ⟨v₁, hv₁0, htraj₁⟩ := exists_trajectory hadm hθ hC1 hC2 (u := fun _ => 1.8)
    (w := fun _ => 0) continuous_const continuous_const (a := 0) (b := 4) (by norm_num)
    (hw 0 4) hv₀
  have hsafe₁ := htraj₁.safe hadm hθ (by rw [hv₁0]; exact hv₀) 4 ⟨by norm_num, le_rfl⟩
  -- second piece: input low on [4, 10], started where the first piece ended
  obtain ⟨v₂, hv₂4, htraj₂⟩ := exists_trajectory hadm hθ hC1 hC2 (u := fun _ => 0)
    (w := fun _ => 0) continuous_const continuous_const (a := 4) (b := 10) (by norm_num)
    (hw 4 10) hsafe₁
  have h₁ : IsTrajectory illustrative nominal uStepR v₁ 0 4 :=
    IsTrajectory.congr_input htraj₁ (fun t ht => by simp [uStepR, ht.2])
  have h₂ : IsTrajectory illustrative nominal uStepR v₂ 4 10 :=
    IsTrajectory.congr_input htraj₂ (fun t ht => by simp [uStepR, not_lt.mpr ht.1])
  refine ⟨fun t => if t < 4 then v₁ t else v₂ t, by simp [hv₁0],
    IsTrajectory.concat h₁ h₂ (by norm_num) (by norm_num) hv₂4.symm⟩

/-- The two step inputs differ only at the instant `t = 4`. -/
theorem uStepR_eq_off_jump {t : ℝ} (ht : t ≠ 4) :
    uStepR t = (if t ≤ 4 then (1.8 : ℝ) else 0) := by
  rcases lt_or_gt_of_ne ht with h | h
  · simp [uStepR, h, h.le]
  · simp [uStepR, not_lt.mpr h.le, not_le.mpr h]

end Review.P02

#print axioms Review.P02.IsTrajectory.concat
#print axioms Review.P02.stepR_has_trajectory
