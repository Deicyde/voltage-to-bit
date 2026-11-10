import Mathlib.Analysis.ODE.ExistUnique
import VoltageToBit.Proofs.Guarantee

/-!
# Trajectories exist

The guarantee in `Proofs/Guarantee.lean` quantifies over all trajectories. This
file shows the quantifier is not empty.

* `IsTrajectory.of_ode`: every solution of the ordinary differential equation
  `Cf (v) * dv/dt = Inet θ u v + w t`, with parameters `θ` in the box, a
  capacitance function `Cf` within `[Clo, Chi]` and a disturbance `|w| ≤ eps`,
  is a trajectory of the inclusion. `IsTrajectory.of_ode_varying` allows the
  parameter point to move within the box as time passes.
* `exists_solution`: for continuous input `u`, continuous disturbance `w` with
  `|w| ≤ eps` on `[a, b]`, a voltage-dependent capacitance `Cf` that stays in
  `[Clo, Chi]` and is Lipschitz on the safe domain, and any initial state in the
  safe domain, the ODE has a solution on all of `[a, b]`.
  The proof applies Picard–Lindelöf to a vector field clamped to the safe
  domain (so it is globally Lipschitz and bounded, giving a solution on the
  whole interval at once) and then uses the boundary margins to show that the
  solution never leaves the safe domain, where clamping does nothing.
* `exists_trajectory`: the combination.
* `solution_unique`: two solutions with the same initial state coincide.

Scope: existence and uniqueness are proved for constant parameters, continuous
`u` and `w`, and Lipschitz `Cf`. The guarantee itself needs none of this; for
less regular data, or parameters that move within the box, it is a statement
about whatever trajectories there are.

The capacitance bounds are required for all real arguments. In every lemma of
this file that takes a capacitance function `Cf`, the hypothesis reads
`∀ x, D.Clo ≤ Cf x` (with `Cf x ≤ D.Chi` where the upper bound is needed), for
every real `x` and not only for `x` in the safe domain; only the Lipschitz
condition is restricted to the safe domain. A capacitance model that is known
only on the safe domain therefore has to be extended to all of `ℝ` before
these lemmas apply, for example by clamping its argument:
`fun x => Cf (clamp D.Vlo D.Vhi x)` agrees with `Cf` on the safe domain and
takes no other values. The lemmas then speak about solutions of the extended
model. For an admissible record such a solution stays in the safe domain if it
starts there (`exists_solution`, `IsTrajectory.safe`), and there the extended
model is the original one.
-/

namespace VoltageToBit

open Set Metric
open scoped NNReal Topology

/-- The inclusion contains the ODE model with an arbitrary capacitance function
within the bounds, a parameter point that may move within the box as time
passes, and an arbitrary disturbance within the bound. -/
theorem IsTrajectory.of_ode_varying {D : Design} {θ : ℝ → Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hθ : ∀ t ∈ Ico a b, D.InBox (θ t))
    (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet (θ t) (u t) (v t) + w t) :
    IsTrajectory D u v a b where
  cont := hcont
  incl := fun t ht => by
    obtain ⟨v', hd, he⟩ := hode t ht
    refine ⟨v', Cf (v t), hd, (hCf _).1, (hCf _).2, fun _ => ⟨θ t, hθ t ht, ?_⟩⟩
    rw [he, add_sub_cancel_left]
    exact hw t ht

/-- The inclusion contains the ODE model with constant parameters in the box,
an arbitrary capacitance function within the bounds and an arbitrary
disturbance within the bound.

The bounds on `Cf` are required for all real arguments (`hCf`), not only on the
safe domain. A capacitance model known only on the safe domain has to be
extended first, for example by clamping its argument
(`fun x => Cf (clamp D.Vlo D.Vhi x)`); see the header of this file. -/
theorem IsTrajectory.of_ode {D : Design} {θ : Params} {u v : ℝ → ℝ} {a b : ℝ}
    {Cf w : ℝ → ℝ} (hθ : D.InBox θ) (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ D.eps) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t) :
    IsTrajectory D u v a b :=
  IsTrajectory.of_ode_varying (θ := fun _ => θ) (fun _ _ => hθ) hCf hw hcont hode

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

/-- The ODE right-hand side with the state clamped to the safe domain. -/
noncomputable def clampedField (D : Design) (θ : Params) (Cf u w : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (Inet θ (u t) (clamp D.Vlo D.Vhi x) + w t) / Cf (clamp D.Vlo D.Vhi x)

/-- The clamped right-hand side is Lipschitz in the state and bounded,
uniformly in time on a compact interval. -/
theorem exists_clampedField_bounds {D : Design} {θ : Params} (hD : D.Admissible)
    (hθ : D.InBox θ) {Cf : ℝ → ℝ} (hCf : ∀ x, D.Clo ≤ Cf x) {Kc : ℝ}
    (hCfLip : ∀ x ∈ D.Safe, ∀ y ∈ D.Safe, |Cf x - Cf y| ≤ Kc * |x - y|)
    {u w : ℝ → ℝ} (hu : Continuous u) (hw : Continuous w) (a b : ℝ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
      (∀ t ∈ Icc a b, ∀ x y : ℝ,
        |clampedField D θ Cf u w t x - clampedField D θ Cf u w t y| ≤ K * |x - y|) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ, |clampedField D θ Cf u w t x| ≤ L) := by
  have hClo : 0 < D.Clo := hD.C_pos
  have hCpos : ∀ x, 0 < Cf x := fun x => lt_of_lt_of_le hClo (hCf x)
  have hdom : D.Vlo ≤ D.Vhi := by linarith [hD.Vlo_le, hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  have hkp : 0 ≤ θ.kp := le_trans hD.kp_pos.le hθ.kp_ge
  have hkn : 0 ≤ θ.kn := le_trans hD.kn_pos.le hθ.kn_ge
  -- a bound on the input over the compact time interval
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hu.continuousOn
  -- a bound on the numerator `Inet + w` over time × safe domain
  have hNcont : Continuous (fun p : ℝ × ℝ => Inet θ (u p.1) p.2 + w p.1) := by
    have hI := (continuous_Inet θ).comp ((hu.comp continuous_fst).prodMk continuous_snd)
    exact hI.add (hw.comp continuous_fst)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc D.Vlo D.Vhi) hNcont.continuousOn
  have hNbound : ∀ t ∈ Icc a b, ∀ x : ℝ,
      |Inet θ (u t) (clamp D.Vlo D.Vhi x) + w t| ≤ |M₀| := by
    intro t ht x
    have := hM₀ (t, clamp D.Vlo D.Vhi x) ⟨ht, clamp_mem hdom x⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  -- Lipschitz constant of the numerator in the state
  set Y : ℝ := max |D.Vlo| |D.Vhi| with hY
  set K₀ : ℝ := θ.kp * (Y + |U| + |θ.Vtp|) + θ.kn * (Y + |U| + |θ.Vtn|) with hK₀def
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) (le_max_left _ _)
  have hK₀ : 0 ≤ K₀ := by positivity
  have hNLip : ∀ t ∈ Icc a b, ∀ x y : ℝ,
      |Inet θ (u t) (clamp D.Vlo D.Vhi x) - Inet θ (u t) (clamp D.Vlo D.Vhi y)|
        ≤ K₀ * |x - y| := by
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
    exact h1.trans (mul_le_mul hmod h2 (abs_nonneg _) hK₀)
  refine ⟨K₀ / D.Clo + |M₀| * |Kc| / (D.Clo * D.Clo), |M₀| / D.Clo, by positivity, by positivity,
    fun t ht x y => ?_, fun t ht x => ?_⟩
  · -- Lipschitz in the state
    have hx := clamp_mem hdom x
    have hy := clamp_mem hdom y
    have hCx := hCf (clamp D.Vlo D.Vhi x)
    have hCy := hCf (clamp D.Vlo D.Vhi y)
    have hCxpos := hCpos (clamp D.Vlo D.Vhi x)
    have hCypos := hCpos (clamp D.Vlo D.Vhi y)
    have hC : |Cf (clamp D.Vlo D.Vhi x) - Cf (clamp D.Vlo D.Vhi y)| ≤ |Kc| * |x - y| := by
      refine (hCfLip _ hx _ hy).trans ?_
      refine (mul_le_mul_of_nonneg_right (le_abs_self Kc) (abs_nonneg _)).trans ?_
      exact mul_le_mul_of_nonneg_left (abs_clamp_sub_le _ _ x y) (abs_nonneg _)
    have hsplit : clampedField D θ Cf u w t x - clampedField D θ Cf u w t y
        = (Inet θ (u t) (clamp D.Vlo D.Vhi x) - Inet θ (u t) (clamp D.Vlo D.Vhi y))
            / Cf (clamp D.Vlo D.Vhi x)
          - (Inet θ (u t) (clamp D.Vlo D.Vhi y) + w t)
              * (Cf (clamp D.Vlo D.Vhi x) - Cf (clamp D.Vlo D.Vhi y))
              / (Cf (clamp D.Vlo D.Vhi x) * Cf (clamp D.Vlo D.Vhi y)) := by
      unfold clampedField
      field_simp
      ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    have t1 : |(Inet θ (u t) (clamp D.Vlo D.Vhi x) - Inet θ (u t) (clamp D.Vlo D.Vhi y))
        / Cf (clamp D.Vlo D.Vhi x)| ≤ K₀ * |x - y| / D.Clo := by
      rw [abs_div, abs_of_pos hCxpos]
      exact div_le_div₀ (mul_nonneg hK₀ (abs_nonneg _)) (hNLip t ht x y) hClo hCx
    have t2 : |(Inet θ (u t) (clamp D.Vlo D.Vhi y) + w t)
          * (Cf (clamp D.Vlo D.Vhi x) - Cf (clamp D.Vlo D.Vhi y))
          / (Cf (clamp D.Vlo D.Vhi x) * Cf (clamp D.Vlo D.Vhi y))|
        ≤ |M₀| * (|Kc| * |x - y|) / (D.Clo * D.Clo) := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hCxpos hCypos)]
      exact div_le_div₀ (by positivity)
        (mul_le_mul (hNbound t ht y) hC (abs_nonneg _) (abs_nonneg _)) (mul_pos hClo hClo)
        (mul_le_mul hCx hCy hClo.le hCxpos.le)
    have e : (K₀ / D.Clo + |M₀| * |Kc| / (D.Clo * D.Clo)) * |x - y|
        = K₀ * |x - y| / D.Clo + |M₀| * (|Kc| * |x - y|) / (D.Clo * D.Clo) := by
      ring
    rw [e]
    exact add_le_add t1 t2
  · -- bounded
    unfold clampedField
    rw [abs_div, abs_of_pos (hCpos _)]
    exact div_le_div₀ (abs_nonneg _) (hNbound t ht x) hClo (hCf _)

/-- **Existence.** For continuous input and disturbance, a capacitance function
that stays at or above `Clo` and is Lipschitz on the safe domain, and an
initial state in the safe domain, the ODE `Cf (v) * dv/dt = Inet θ u v + w` has
a solution on the whole interval `[a, b]`, and it stays in the safe domain.

The bound `Clo ≤ Cf x` is required for all real `x` (`hCf`), not only on the
safe domain; only the Lipschitz condition `hCfLip` is restricted to the safe
domain. A capacitance model known only on the safe domain has to be extended
first, for example by clamping its argument
(`fun x => Cf (clamp D.Vlo D.Vhi x)`). The solution obtained stays in the safe
domain, where the extension agrees with the model. -/
theorem exists_solution {D : Design} {θ : Params} (hD : D.Admissible) (hθ : D.InBox θ)
    {Cf : ℝ → ℝ} (hCf : ∀ x, D.Clo ≤ Cf x) {Kc : ℝ}
    (hCfLip : ∀ x ∈ D.Safe, ∀ y ∈ D.Safe, |Cf x - Cf y| ≤ Kc * |x - y|)
    {u w : ℝ → ℝ} (hu : Continuous u) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps) {v₀ : ℝ}
    (hv₀ : v₀ ∈ D.Safe) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ (∀ t ∈ Icc a b, v t ∈ D.Safe) ∧
      ∀ t ∈ Icc a b,
        HasDerivWithinAt v ((Inet θ (u t) (v t) + w t) / Cf (v t)) (Icc a b) t := by
  have hCpos : ∀ x, 0 < Cf x := fun x => lt_of_lt_of_le hD.C_pos (hCf x)
  have hdom : D.Vlo ≤ D.Vhi := by linarith [hD.Vlo_le, hD.VDD_pos, hD.VDD_le, hD.Vhi_ge]
  obtain ⟨K, L, hK, hL, hLip, hnorm⟩ := exists_clampedField_bounds hD hθ hCf hCfLip hu hw a b
  -- Picard–Lindelöf on the whole interval
  have hPL : IsPicardLindelof (clampedField D θ Cf u w) (tmin := a) (tmax := b)
      ⟨a, left_mem_Icc.mpr hab⟩ v₀
      (⟨L * (b - a), mul_nonneg hL (sub_nonneg.mpr hab)⟩ : ℝ≥0) 0
      (⟨L, hL⟩ : ℝ≥0) (⟨K, hK⟩ : ℝ≥0) :=
    { lipschitzOnWith := fun t ht => by
        refine LipschitzWith.lipschitzOnWith ?_
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        rw [Real.dist_eq, Real.dist_eq]
        exact hLip t ht x y
      continuousOn := fun x _ => by
        have : Continuous (fun t => clampedField D θ Cf u w t x) := by
          have hI := (continuous_Inet θ).comp
            (hu.prodMk (continuous_const (y := clamp D.Vlo D.Vhi x)))
          exact (hI.add hw).div_const _
        exact this.continuousOn
      norm_le := fun t ht x _ => by
        rw [Real.norm_eq_abs]
        exact hnorm t ht x
      mul_max_le := by
        have hmax : max (b - a) (a - a) = b - a := by
          rw [sub_self]
          exact max_eq_left (sub_nonneg.mpr hab)
        show L * max (b - a) (a - a) ≤ L * (b - a) - 0
        rw [hmax, sub_zero] }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α a = v₀ := hα0
  have hαcont : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousWithinAt
  have hαr : ∀ t ∈ Ico a b, HasDerivWithinAt α (clampedField D θ Cf u w t (α t)) (Ici t) t :=
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
      exact div_pos (by linarith) (hCpos _)
    · refine barrier_le hαcont hαr (by rw [hα0']; exact hv₀.2) ?_ t ht
      intro s hs hvs
      have hI := Design.Inet_Vhi_lt hD hθ (u s)
      have hw' := abs_le.mp (hwb s (Ico_subset_Icc_self hs))
      have hcl : clamp D.Vlo D.Vhi D.Vhi = D.Vhi := clamp_of_mem (right_mem_Icc.mpr hdom)
      unfold clampedField
      rw [hvs, hcl]
      exact div_neg_of_neg_of_pos (by linarith) (hCpos _)
  -- inside the safe domain the clamp is the identity
  refine ⟨α, hα0', hsafe, fun t ht => ?_⟩
  have h := hα t ht
  unfold clampedField at h
  rwa [clamp_of_mem (hsafe t ht)] at h

/-- **Trajectories exist.** Under the hypotheses of `exists_solution`, with the
capacitance function also bounded above by `Chi`, there is a trajectory of the
inclusion on `[a, b]` from any initial state in the safe domain. -/
theorem exists_trajectory {D : Design} {θ : Params} (hD : D.Admissible) (hθ : D.InBox θ)
    {Cf : ℝ → ℝ} (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi) {Kc : ℝ}
    (hCfLip : ∀ x ∈ D.Safe, ∀ y ∈ D.Safe, |Cf x - Cf y| ≤ Kc * |x - y|)
    {u w : ℝ → ℝ} (hu : Continuous u) (hw : Continuous w) {a b : ℝ} (hab : a ≤ b)
    (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps) {v₀ : ℝ} (hv₀ : v₀ ∈ D.Safe) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ IsTrajectory D u v a b := by
  obtain ⟨v, hv0, -, hode⟩ :=
    exists_solution hD hθ (fun x => (hCf x).1) hCfLip hu hw hab hwb hv₀
  have hCpos : ∀ x, 0 < Cf x := fun x => lt_of_lt_of_le hD.C_pos (hCf x).1
  refine ⟨v, hv0, IsTrajectory.of_ode hθ (Cf := Cf) (w := w) hCf
    (fun t ht => hwb t (Ico_subset_Icc_self ht))
    (fun t ht => (hode t ht).continuousWithinAt) (fun t ht => ?_)⟩
  refine ⟨_, (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht), ?_⟩
  have := (hCpos (v t)).ne'
  field_simp

/-- Trajectories exist for every constant capacitance in range. -/
theorem exists_trajectory_const {D : Design} {θ : Params} (hD : D.Admissible)
    (hθ : D.InBox θ) {C : ℝ} (hC1 : D.Clo ≤ C) (hC2 : C ≤ D.Chi) {u w : ℝ → ℝ}
    (hu : Continuous u) (hw : Continuous w) {a b : ℝ} (hab : a ≤ b)
    (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps) {v₀ : ℝ} (hv₀ : v₀ ∈ D.Safe) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ IsTrajectory D u v a b :=
  exists_trajectory hD hθ (Cf := fun _ => C) (Kc := 0) (fun _ => ⟨hC1, hC2⟩)
    (fun x _ y _ => by simp) hu hw hab hwb hv₀

/-- **Uniqueness.** Two solutions of the ODE on `[a, b]` that start at the same
point of the safe domain coincide on `[a, b]`. Together with `exists_solution`
this makes the ODE model well posed: for given continuous input and
disturbance and a Lipschitz capacitance in range, the output waveform is a
function of the initial state. -/
theorem solution_unique {D : Design} {θ : Params} (hD : D.Admissible) (hθ : D.InBox θ)
    {Cf : ℝ → ℝ} (hCf : ∀ x, D.Clo ≤ Cf x ∧ Cf x ≤ D.Chi) {Kc : ℝ}
    (hCfLip : ∀ x ∈ D.Safe, ∀ y ∈ D.Safe, |Cf x - Cf y| ≤ Kc * |x - y|)
    {u w : ℝ → ℝ} (hu : Continuous u) (hw : Continuous w) {a b : ℝ}
    (hwb : ∀ t ∈ Icc a b, |w t| ≤ D.eps) {v₁ v₂ : ℝ → ℝ}
    (h₁ : ∀ t ∈ Icc a b,
      HasDerivWithinAt v₁ ((Inet θ (u t) (v₁ t) + w t) / Cf (v₁ t)) (Icc a b) t)
    (h₂ : ∀ t ∈ Icc a b,
      HasDerivWithinAt v₂ ((Inet θ (u t) (v₂ t) + w t) / Cf (v₂ t)) (Icc a b) t)
    (h0 : v₁ a = v₂ a) (hs : v₁ a ∈ D.Safe) : EqOn v₁ v₂ (Icc a b) := by
  have hCpos : ∀ x, 0 < Cf x := fun x => lt_of_lt_of_le hD.C_pos (hCf x).1
  -- both solutions are trajectories, hence stay in the safe domain
  have traj : ∀ v : ℝ → ℝ, (∀ t ∈ Icc a b,
      HasDerivWithinAt v ((Inet θ (u t) (v t) + w t) / Cf (v t)) (Icc a b) t) →
      IsTrajectory D u v a b := fun v hv =>
    IsTrajectory.of_ode hθ (Cf := Cf) (w := w) hCf
      (fun t ht => hwb t (Ico_subset_Icc_self ht))
      (fun t ht => (hv t ht).continuousWithinAt)
      (fun t ht => ⟨_, (hv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht), by have := (hCpos (v t)).ne'; field_simp⟩)
  have hsafe₁ := (traj v₁ h₁).safe hD hs
  have hsafe₂ := (traj v₂ h₂).safe hD (h0 ▸ hs)
  obtain ⟨K, L, hK, -, hLip, -⟩ :=
    exists_clampedField_bounds hD hθ (fun x => (hCf x).1) hCfLip hu hw a b
  -- on the safe domain the right-hand side is the clamped field
  have conv : ∀ v : ℝ → ℝ, (∀ t ∈ Icc a b,
      HasDerivWithinAt v ((Inet θ (u t) (v t) + w t) / Cf (v t)) (Icc a b) t) →
      (∀ t ∈ Icc a b, v t ∈ D.Safe) →
      ∀ t ∈ Ico a b, HasDerivWithinAt v (clampedField D θ Cf u w t (v t)) (Ici t) t := by
    intro v hv hsafe t ht
    have h := (hv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    unfold clampedField
    rwa [clamp_of_mem (hsafe t (Ico_subset_Icc_self ht))]
  exact ODE_solution_unique_of_mem_Icc_right (K := ⟨K, hK⟩) (s := fun _ => univ)
    (v := clampedField D θ Cf u w)
    (fun t ht => by
      refine LipschitzWith.lipschitzOnWith ?_
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq]
      exact hLip t (Ico_subset_Icc_self ht) x y)
    (fun t ht => (h₁ t ht).continuousWithinAt) (conv v₁ h₁ hsafe₁) (fun _ _ => mem_univ _)
    (fun t ht => (h₂ t ht).continuousWithinAt) (conv v₂ h₂ hsafe₂) (fun _ _ => mem_univ _) h0

end VoltageToBit
