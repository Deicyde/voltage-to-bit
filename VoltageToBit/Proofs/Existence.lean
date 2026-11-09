import Mathlib.Analysis.ODE.ExistUnique
import VoltageToBit.Proofs.Guarantee

/-!
# Trajectories exist

The guarantee in `Proofs/Guarantee.lean` quantifies over all trajectories. This
file shows the quantifier is not empty.

* `IsTrajectory.of_ode`: every solution of the ordinary differential equation
  `Cf (v) * dv/dt = Inet θ u v + w t`, with a capacitance function `Cf` within
  `[Clo, Chi]` and a disturbance `|w| ≤ eps`, is a trajectory of the inclusion.
* `exists_solution`: for continuous input `u`, continuous disturbance `w` with
  `|w| ≤ eps` on `[a, b]`, a constant capacitance `C ∈ [Clo, Chi]`, and any
  initial state in the safe domain, the ODE has a solution on all of `[a, b]`.
  The proof applies Picard–Lindelöf to a vector field clamped to the safe
  domain (so it is globally Lipschitz and bounded, giving a solution on the
  whole interval at once) and then uses the boundary margins to show that the
  solution never leaves the safe domain, where clamping does nothing.
* `exists_trajectory`: the combination.

Existence is proved for a constant capacitance. The guarantee itself covers
any state- or time-dependent capacitance within the bounds; existence for
those is not proved here.
-/

namespace VoltageToBit

open Set Metric
open scoped NNReal Topology

/-- The inclusion contains the ODE model with an arbitrary capacitance function
within the bounds and an arbitrary disturbance within the bound. -/
theorem IsTrajectory.of_ode {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t) :
    IsTrajectory D θ u v a b where
  cont := hcont
  incl := fun t ht => by
    obtain ⟨v', hd, he⟩ := hode t ht
    refine ⟨v', Cf (v t), hd, (hCf _).1, (hCf _).2, fun _ => ?_⟩
    rw [he, add_sub_cancel_left]
    exact hw t ht

/-- Clamp a real number to `[lo, hi]`. -/
def clamp (lo hi x : ℝ) : ℝ := max (min x hi) lo

theorem clamp_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clamp lo hi x ∈ Icc lo hi :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) h⟩

theorem clamp_of_mem {lo hi x : ℝ} (hx : x ∈ Icc lo hi) : clamp lo hi x = x := by
  unfold clamp
  rw [min_eq_left hx.2, max_eq_left hx.1]

theorem abs_clamp_sub_le (lo hi x y : ℝ) : |clamp lo hi x - clamp lo hi y| ≤ |x - y| := by
  unfold clamp
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem continuous_clamp (lo hi : ℝ) : Continuous (clamp lo hi) := by
  unfold clamp
  fun_prop

/-- The ODE right-hand side with the state clamped to the safe domain. -/
noncomputable def clampedField (D : Design) (θ : Params) (C : ℝ) (u w : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (Inet θ (u t) (clamp D.Vlo D.Vhi x) + w t) / C

/-- **Existence.** For continuous input and disturbance, constant capacitance in
range, and an initial state in the safe domain, the ODE has a solution on the
whole interval `[a, b]`, and it stays in the safe domain. -/
theorem exists_solution {D : Design} {θ : Params} (hD : D.Admissible) (hθ : D.InBox θ)
    {C : ℝ} (hC1 : D.Clo ≤ C) {u w : ℝ → ℝ} (hu : Continuous u) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps) {v₀ : ℝ}
    (hv₀ : v₀ ∈ D.Safe) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ (∀ t ∈ Icc a b, v t ∈ D.Safe) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt v ((Inet θ (u t) (v t) + w t) / C) (Icc a b) t := by
  have hCpos : 0 < C := lt_of_lt_of_le hD.C_pos hC1
  have hdom : D.Vlo ≤ D.Vhi := by linarith [hD.Vlo_le, hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  -- a bound on the input over the compact time interval
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hu.continuousOn
  -- Lipschitz constant of the clamped field in the state
  set Y : ℝ := max |D.Vlo| |D.Vhi| with hY
  set K₀ : ℝ := θ.kp * (Y + |U| + |θ.Vtp|) + θ.kn * (Y + |U| + |θ.Vtn|) with hK₀def
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) (le_max_left _ _)
  have hK₀ : 0 ≤ K₀ := by positivity
  have hLip : ∀ t ∈ Icc a b, ∀ x y : ℝ,
      |clampedField D θ C u w t x - clampedField D θ C u w t y| ≤ K₀ / C * |x - y| := by
    intro t ht x y
    have hx := clamp_mem hdom x
    have hy := clamp_mem hdom y
    have hut : |u t| ≤ |U| := by
      have := hU t ht
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self U)
    have habsx : |clamp D.Vlo D.Vhi x| ≤ Y := abs_le_max_abs_abs hx.1 hx.2
    have habsy : |clamp D.Vlo D.Vhi y| ≤ Y := abs_le_max_abs_abs hy.1 hy.2
    have h1 := abs_Inet_sub_le θ hkn hkp (u t) (clamp D.Vlo D.Vhi x) (clamp D.Vlo D.Vhi y)
    have h2 := abs_clamp_sub_le D.Vlo D.Vhi x y
    have tri : ∀ p q r : ℝ, |p - q - r| ≤ |p| + |q| + |r| := fun p q r =>
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    have b1 := tri (clamp D.Vlo D.Vhi x) (u t) θ.Vtp
    have b2 := tri (clamp D.Vlo D.Vhi y) (u t) θ.Vtp
    have b3 := tri (u t) (clamp D.Vlo D.Vhi x) θ.Vtn
    have b4 := tri (u t) (clamp D.Vlo D.Vhi y) θ.Vtn
    have hmod : θ.kp / 2 * (|clamp D.Vlo D.Vhi x - u t - θ.Vtp| + |clamp D.Vlo D.Vhi y - u t - θ.Vtp|)
        + θ.kn / 2 * (|u t - clamp D.Vlo D.Vhi x - θ.Vtn| + |u t - clamp D.Vlo D.Vhi y - θ.Vtn|)
        ≤ K₀ := by
      have e1 : θ.kp / 2 * (|clamp D.Vlo D.Vhi x - u t - θ.Vtp| + |clamp D.Vlo D.Vhi y - u t - θ.Vtp|)
          ≤ θ.kp / 2 * (2 * (Y + |U| + |θ.Vtp|)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have e2 : θ.kn / 2 * (|u t - clamp D.Vlo D.Vhi x - θ.Vtn| + |u t - clamp D.Vlo D.Vhi y - θ.Vtn|)
          ≤ θ.kn / 2 * (2 * (Y + |U| + |θ.Vtn|)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rw [hK₀def]
      linarith
    have hdiff : |Inet θ (u t) (clamp D.Vlo D.Vhi x) - Inet θ (u t) (clamp D.Vlo D.Vhi y)|
        ≤ K₀ * |x - y| :=
      h1.trans (mul_le_mul hmod h2 (abs_nonneg _) hK₀)
    have e : clampedField D θ C u w t x - clampedField D θ C u w t y
        = (Inet θ (u t) (clamp D.Vlo D.Vhi x) - Inet θ (u t) (clamp D.Vlo D.Vhi y)) / C := by
      unfold clampedField; ring
    rw [e, abs_div, abs_of_pos hCpos, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hdiff hCpos.le
  -- a bound on the clamped field
  have hGcont : Continuous (fun p : ℝ × ℝ => (Inet θ (u p.1) p.2 + w p.1) / C) := by
    have hI := (continuous_Inet θ).comp ((hu.comp continuous_fst).prodMk continuous_snd)
    exact (hI.add (hw.comp continuous_fst)).div_const C
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc D.Vlo D.Vhi) hGcont.continuousOn
  have hnorm : ∀ t ∈ Icc a b, ∀ x : ℝ, |clampedField D θ C u w t x| ≤ |L₀| := by
    intro t ht x
    have := hL₀ (t, clamp D.Vlo D.Vhi x) ⟨ht, clamp_mem hdom x⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  -- Picard–Lindelöf on the whole interval
  have hPL : IsPicardLindelof (clampedField D θ C u w) (tmin := a) (tmax := b)
      ⟨a, left_mem_Icc.mpr hab⟩ v₀
      (⟨|L₀| * (b - a), mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hab)⟩ : ℝ≥0) 0
      (⟨|L₀|, abs_nonneg _⟩ : ℝ≥0) (⟨K₀ / C, div_nonneg hK₀ hCpos.le⟩ : ℝ≥0) :=
    { lipschitzOnWith := fun t ht => by
        refine LipschitzWith.lipschitzOnWith ?_
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        rw [Real.dist_eq, Real.dist_eq]
        exact hLip t ht x y
      continuousOn := fun x _ => by
        have : Continuous (fun t => clampedField D θ C u w t x) := by
          have hI := (continuous_Inet θ).comp (hu.prodMk (continuous_const (y := clamp D.Vlo D.Vhi x)))
          exact (hI.add hw).div_const C
        exact this.continuousOn
      norm_le := fun t ht x _ => by
        rw [Real.norm_eq_abs]
        exact hnorm t ht x
      mul_max_le := by
        have hmax : max (b - a) (a - a) = b - a := by
          rw [sub_self]
          exact max_eq_left (sub_nonneg.mpr hab)
        show |L₀| * max (b - a) (a - a) ≤ |L₀| * (b - a) - 0
        rw [hmax, sub_zero] }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α a = v₀ := hα0
  have hαcont : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousWithinAt
  have hαr : ∀ t ∈ Ico a b, HasDerivWithinAt α (clampedField D θ C u w t (α t)) (Ici t) t :=
    fun t ht => (hα t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  -- the solution of the clamped problem stays in the safe domain
  have hsafe : ∀ t ∈ Icc a b, α t ∈ D.Safe := by
    intro t ht
    constructor
    · refine barrier_ge hαcont hαr (by rw [hα0']; exact hv₀.1) ?_ t ht
      intro s hs hvs
      have hI := Design.Inet_Vlo_gt hD hθ (u s)
      have hw' := abs_le.mp (hwb s (Ico_subset_Icc_self hs))
      have hcl : clamp D.Vlo D.Vhi D.Vlo = D.Vlo := clamp_of_mem (left_mem_Icc.mpr hdom)
      unfold clampedField
      rw [hvs, hcl]
      exact div_pos (by linarith) hCpos
    · refine barrier_le hαcont hαr (by rw [hα0']; exact hv₀.2) ?_ t ht
      intro s hs hvs
      have hI := Design.Inet_Vhi_lt hD hθ (u s)
      have hw' := abs_le.mp (hwb s (Ico_subset_Icc_self hs))
      have hcl : clamp D.Vlo D.Vhi D.Vhi = D.Vhi := clamp_of_mem (right_mem_Icc.mpr hdom)
      unfold clampedField
      rw [hvs, hcl]
      exact div_neg_of_neg_of_pos (by linarith) hCpos
  -- inside the safe domain the clamp is the identity
  refine ⟨α, hα0', hsafe, fun t ht => ?_⟩
  have h := hα t ht
  unfold clampedField at h
  rwa [clamp_of_mem (hsafe t ht)] at h

/-- **Trajectories exist.** Under the hypotheses of `exists_solution`, there is
a trajectory of the inclusion on `[a, b]` from any initial state in the safe
domain. -/
theorem exists_trajectory {D : Design} {θ : Params} (hD : D.Admissible) (hθ : D.InBox θ)
    {C : ℝ} (hC1 : D.Clo ≤ C) (hC2 : C ≤ D.Chi) {u w : ℝ → ℝ} (hu : Continuous u)
    (hw : Continuous w) {a b : ℝ} (hab : a ≤ b) (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps)
    {v₀ : ℝ} (hv₀ : v₀ ∈ D.Safe) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ IsTrajectory D θ u v a b := by
  obtain ⟨v, hv0, -, hode⟩ := exists_solution hD hθ hC1 hu hw hab hwb hv₀
  have hCpos : 0 < C := lt_of_lt_of_le hD.C_pos hC1
  refine ⟨v, hv0, IsTrajectory.of_ode (Cf := fun _ => C) (w := w) (fun _ => ⟨hC1, hC2⟩)
    (fun t ht => hwb t (Ico_subset_Icc_self ht))
    (fun t ht => (hode t ht).continuousWithinAt) (fun t ht => ?_)⟩
  refine ⟨_, (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht), ?_⟩
  field_simp

end VoltageToBit
