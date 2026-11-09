import VoltageToBit.Proofs.Existence

/-!
# Gluing trajectories, and existence for a step input

The trajectory notion is pointwise in time: at each instant it relates the
right derivative of the output to the value of the input at that same instant.
Two consequences are recorded here.

* `IsTrajectory.congr_input`: only the input values on `[a, b)` matter.
* `IsTrajectory.concat`: trajectories on `[a, c]` and `[c, b]` that agree at
  `c` glue to a trajectory on `[a, b]`.
* `exists_trajectory_step`: trajectories exist for an input with one jump, of
  the form "`u₁` before `c`, `u₂` from `c` on" with `u₁`, `u₂` continuous.
  This covers the ideal digital edge.

A caution that follows from the same pointwise character. The value the input
takes *at* a jump instant matters: the step above is right-continuous (it takes
the new value at `c`). For an input that keeps its old value at the jump
instant and takes the new value only strictly after it, the right derivative
of any candidate output is dictated by the new value while the inclusion at
that instant refers to the old one, so in general no trajectory exists on an
interval containing the jump and the guarantee says nothing. Existence is
proved here only for continuous inputs and for right-continuous steps.
-/

namespace VoltageToBit

open Set Filter
open scoped Topology

namespace IsTrajectory

variable {D : Design} {u u' : ℝ → ℝ} {a b c : ℝ}

/-- A trajectory depends on the input only through its values on `[a, b)`. -/
theorem congr_input {v : ℝ → ℝ} (h : IsTrajectory D u v a b)
    (hu : ∀ t ∈ Ico a b, u t = u' t) : IsTrajectory D u' v a b where
  cont := h.cont
  incl := fun t ht => by
    obtain ⟨d, cap, hd, hc1, hc2, hb⟩ := h.incl t ht
    exact ⟨d, cap, hd, hc1, hc2, by rw [← hu t ht]; exact hb⟩

/-- Trajectories on `[a, c]` and `[c, b]` that agree at `c` glue to a
trajectory on `[a, b]`. -/
theorem concat {v₁ v₂ : ℝ → ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (h₁ : IsTrajectory D u v₁ a c) (h₂ : IsTrajectory D u v₂ c b) (hc : v₁ c = v₂ c) :
    IsTrajectory D u (fun t => if t ≤ c then v₁ t else v₂ t) a b := by
  set g : ℝ → ℝ := fun t => if t ≤ c then v₁ t else v₂ t with hg
  have hg₁ : ∀ y, y ≤ c → g y = v₁ y := fun y hy => by simp [hg, hy]
  have hg₂ : ∀ y, c ≤ y → g y = v₂ y := fun y hy => by
    rcases eq_or_lt_of_le hy with rfl | hlt
    · simp [hg, hc]
    · simp [hg, not_le.mpr hlt]
  refine ⟨?_, fun t ht => ?_⟩
  · have e1 : ContinuousOn g (Icc a c) := h₁.cont.congr fun t ht => hg₁ t ht.2
    have e2 : ContinuousOn g (Icc c b) := h₂.cont.congr fun t ht => hg₂ t ht.1
    have := e1.union_of_isClosed e2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hac hcb] at this
  · rcases lt_or_ge t c with htc | htc
    · obtain ⟨d, cap, hd, hc1, hc2, hb⟩ := h₁.incl t ⟨ht.1, htc⟩
      refine ⟨d, cap, ?_, hc1, hc2, ?_⟩
      · refine hd.congr_of_eventuallyEq ?_ (hg₁ t htc.le)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)] with y hy
        exact hg₁ y (le_of_lt hy)
      · rw [hg₁ t htc.le]
        exact hb
    · obtain ⟨d, cap, hd, hc1, hc2, hb⟩ := h₂.incl t ⟨htc, ht.2⟩
      refine ⟨d, cap, hd.congr (fun y hy => hg₂ y (le_trans htc hy)) (hg₂ t htc), hc1, hc2, ?_⟩
      rw [hg₂ t htc]
      exact hb

end IsTrajectory

/-- **Existence for a step input.** For an input that follows a continuous
`u₁` before time `c` and a continuous `u₂` from `c` on (so it may jump at `c`,
taking the new value there), constant parameters in the box, a Lipschitz
capacitance in range and a continuous disturbance within the bound, a
trajectory exists on `[a, b]` from any initial state in the safe domain. -/
theorem exists_trajectory_step {D : Design} {θ : Params} (hD : D.Admissible)
    (hθ : D.InBox θ) {Cf : ℝ → ℝ} (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi) {Kc : ℝ}
    (hCfLip : ∀ x ∈ D.Safe, ∀ y ∈ D.Safe, |Cf x - Cf y| ≤ Kc * |x - y|)
    {u₁ u₂ w : ℝ → ℝ} (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (hw : Continuous w)
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps)
    {v₀ : ℝ} (hv₀ : v₀ ∈ D.Safe) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧
      IsTrajectory D (fun t => if t < c then u₁ t else u₂ t) v a b := by
  obtain ⟨v₁, hv₁0, h₁⟩ := exists_trajectory hD hθ hCf hCfLip hu₁ hw hac
    (fun t ht => hwb t ⟨ht.1, le_trans ht.2 hcb⟩) hv₀
  have hsafe : v₁ c ∈ D.Safe := h₁.safe hD (by rw [hv₁0]; exact hv₀) c ⟨hac, le_rfl⟩
  obtain ⟨v₂, hv₂0, h₂⟩ := exists_trajectory hD hθ hCf hCfLip hu₂ hw hcb
    (fun t ht => hwb t ⟨le_trans hac ht.1, ht.2⟩) hsafe
  refine ⟨fun t => if t ≤ c then v₁ t else v₂ t, by simp [hac, hv₁0], ?_⟩
  exact IsTrajectory.concat hac hcb
    (h₁.congr_input fun t ht => by simp [ht.2])
    (h₂.congr_input fun t ht => by simp [not_lt.mpr ht.1]) hv₂0.symm

end VoltageToBit
