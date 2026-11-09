import VoltageToBit.Proofs.Guarantee

/-!
# What another description of the node must satisfy to be covered

The trajectory notion allows, at each instant, any parameter point of the box
and an additive current error of at most `eps`. This file turns that into the
exact obligation linking the square-law model to any other description of the
same node (a higher-fidelity device model, or the physical device).

* `Design.exists_inBox_of_between`: if a current lies between the net currents
  of two box members (each relaxed by `ε`), then some box member reproduces it
  to within `ε`. The box is convex and the device law is continuous in its
  parameters, so the intermediate value theorem applies along the segment.
* `IsTrajectory.of_model_error`: if on the safe domain the "true" net current
  `J t x` is within `εm` of *some* box member's current, and an additional
  disturbance is bounded by `εw`, with `εm + εw ≤ eps`, then every solution of
  `c * v' = J t (v t) + w t` is a trajectory.
* `IsTrajectory.of_sandwich`: the same with the hypothesis in its checkable
  form: `J t x` lies between the currents of two box members, up to `εm`.

So a model whose current is multiplicatively off from one square law (the
typical shape of model-form error) is covered when the parameter box is wide
enough to sandwich it; the additive `eps` only has to absorb what the box does
not, such as conduction below threshold.

These are statements about mathematics only. Whether a physical inverter, or a
SPICE model of one, satisfies the sandwich hypothesis is an empirical question
that this repository does not settle. See `docs/assumptions.md`.

The hypothesis is needed only on the safe domain: `IsTrajectory.safe` shows the
solution never leaves it, so no bound outside the safe domain is ever used.
-/

namespace VoltageToBit

open Set

/-- Componentwise interpolation between two parameter points. -/
def Params.mix (θ₁ θ₂ : Params) (s : ℝ) : Params where
  VDD := θ₁.VDD + s * (θ₂.VDD - θ₁.VDD)
  kn := θ₁.kn + s * (θ₂.kn - θ₁.kn)
  kp := θ₁.kp + s * (θ₂.kp - θ₁.kp)
  Vtn := θ₁.Vtn + s * (θ₂.Vtn - θ₁.Vtn)
  Vtp := θ₁.Vtp + s * (θ₂.Vtp - θ₁.Vtp)

theorem Params.mix_zero (θ₁ θ₂ : Params) : Params.mix θ₁ θ₂ 0 = θ₁ := by
  cases θ₁
  simp [Params.mix]

theorem Params.mix_one (θ₁ θ₂ : Params) : Params.mix θ₁ θ₂ 1 = θ₂ := by
  cases θ₁
  cases θ₂
  simp [Params.mix]

theorem continuous_Inet_mix (θ₁ θ₂ : Params) (u x : ℝ) :
    Continuous (fun s : ℝ => Inet (Params.mix θ₁ θ₂ s) u x) := by
  unfold Inet Ip In Params.mix
  have := continuous_psq
  dsimp only
  fun_prop

namespace Design

variable {D : Design}

private theorem interp_mem {lo hi x y s : ℝ} (hx : lo ≤ x) (hx' : x ≤ hi) (hy : lo ≤ y)
    (hy' : y ≤ hi) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lo ≤ x + s * (y - x) ∧ x + s * (y - x) ≤ hi := by
  constructor
  · nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hy),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hx)]
  · nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hy'),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hx')]

/-- The parameter box is convex. -/
theorem InBox.mix {θ₁ θ₂ : Params} (h₁ : D.InBox θ₁) (h₂ : D.InBox θ₂) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : D.InBox (Params.mix θ₁ θ₂ s) where
  VDD_ge := (interp_mem h₁.VDD_ge h₁.VDD_le h₂.VDD_ge h₂.VDD_le hs.1 hs.2).1
  VDD_le := (interp_mem h₁.VDD_ge h₁.VDD_le h₂.VDD_ge h₂.VDD_le hs.1 hs.2).2
  kn_ge := (interp_mem h₁.kn_ge h₁.kn_le h₂.kn_ge h₂.kn_le hs.1 hs.2).1
  kn_le := (interp_mem h₁.kn_ge h₁.kn_le h₂.kn_ge h₂.kn_le hs.1 hs.2).2
  kp_ge := (interp_mem h₁.kp_ge h₁.kp_le h₂.kp_ge h₂.kp_le hs.1 hs.2).1
  kp_le := (interp_mem h₁.kp_ge h₁.kp_le h₂.kp_ge h₂.kp_le hs.1 hs.2).2
  Vtn_ge := (interp_mem h₁.Vtn_ge h₁.Vtn_le h₂.Vtn_ge h₂.Vtn_le hs.1 hs.2).1
  Vtn_le := (interp_mem h₁.Vtn_ge h₁.Vtn_le h₂.Vtn_ge h₂.Vtn_le hs.1 hs.2).2
  Vtp_ge := (interp_mem h₁.Vtp_ge h₁.Vtp_le h₂.Vtp_ge h₂.Vtp_le hs.1 hs.2).1
  Vtp_le := (interp_mem h₁.Vtp_ge h₁.Vtp_le h₂.Vtp_ge h₂.Vtp_le hs.1 hs.2).2

/-- **Intermediate currents are attained in the box.** If a current `J` lies
between the net currents of two box members, each relaxed by `ε ≥ 0`, then some
box member reproduces `J` to within `ε`. -/
theorem exists_inBox_of_between {θ₁ θ₂ : Params} (h₁ : D.InBox θ₁) (h₂ : D.InBox θ₂)
    {u x J ε : ℝ} (hε : 0 ≤ ε) (hlo : Inet θ₁ u x - ε ≤ J) (hhi : J ≤ Inet θ₂ u x + ε) :
    ∃ θ : Params, D.InBox θ ∧ |J - Inet θ u x| ≤ ε := by
  by_cases hA : J ≤ Inet θ₁ u x
  · exact ⟨θ₁, h₁, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases hB : Inet θ₂ u x ≤ J
  · exact ⟨θ₂, h₂, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  -- strictly between: intermediate value theorem along the segment
  have hmem : J ∈ Icc (Inet (Params.mix θ₁ θ₂ 0) u x) (Inet (Params.mix θ₁ θ₂ 1) u x) := by
    rw [Params.mix_zero, Params.mix_one]
    exact ⟨(not_le.mp hA).le, (not_le.mp hB).le⟩
  obtain ⟨s, hs, hsJ⟩ := intermediate_value_Icc (zero_le_one' ℝ)
    (continuous_Inet_mix θ₁ θ₂ u x).continuousOn hmem
  refine ⟨Params.mix θ₁ θ₂ s, h₁.mix h₂ hs, ?_⟩
  have : J - Inet (Params.mix θ₁ θ₂ s) u x = 0 := by
    have h := hsJ
    simp only at h
    linarith
  rw [this, abs_zero]
  exact hε

end Design

/-- **Model-error embedding.** A solution of a different current law that, on
the safe domain, stays within the error budget of some member of the box is a
trajectory of the uncertain inverter. -/
theorem IsTrajectory.of_model_error {D : Design} {u v : ℝ → ℝ} {a b : ℝ}
    {J : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {εm εw : ℝ} (hbudget : εm + εw ≤ D.eps)
    (hJ : ∀ t ∈ Ico a b, ∀ x ∈ D.Safe,
      ∃ θ : Params, D.InBox θ ∧ |J t x - Inet θ (u t) x| ≤ εm)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ εw)
    (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      D.Clo ≤ c ∧ c ≤ D.Chi ∧ c * v' = J t (v t) + w t) :
    IsTrajectory D u v a b where
  cont := hcont
  incl := fun t ht => by
    obtain ⟨v', c, hd, hc1, hc2, he⟩ := hode t ht
    refine ⟨v', c, hd, hc1, hc2, fun hsafe => ?_⟩
    obtain ⟨θ, hθ, h1⟩ := hJ t ht (v t) hsafe
    have h2 := hw t ht
    refine ⟨θ, hθ, ?_⟩
    have e : c * v' - Inet θ (u t) (v t) = (J t (v t) - Inet θ (u t) (v t)) + w t := by
      rw [he]; ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)

/-- **Sandwich form of the model-error obligation.** It suffices that, on the
safe domain, the other model's current lies between the net currents of two
box members, up to `εm`. The two members may depend on the time and on the
state. -/
theorem IsTrajectory.of_sandwich {D : Design} {u v : ℝ → ℝ} {a b : ℝ}
    {J : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {εm εw : ℝ} (hεm : 0 ≤ εm) (hbudget : εm + εw ≤ D.eps)
    (hJ : ∀ t ∈ Ico a b, ∀ x ∈ D.Safe, ∃ θ₁ θ₂ : Params, D.InBox θ₁ ∧ D.InBox θ₂ ∧
      Inet θ₁ (u t) x - εm ≤ J t x ∧ J t x ≤ Inet θ₂ (u t) x + εm)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ εw)
    (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      D.Clo ≤ c ∧ c ≤ D.Chi ∧ c * v' = J t (v t) + w t) :
    IsTrajectory D u v a b :=
  IsTrajectory.of_model_error hbudget
    (fun t ht x hx => by
      obtain ⟨θ₁, θ₂, h₁, h₂, hlo, hhi⟩ := hJ t ht x hx
      exact Design.exists_inBox_of_between h₁ h₂ hεm hlo hhi)
    hw hcont hode

end VoltageToBit
