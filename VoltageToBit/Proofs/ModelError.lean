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
* `IsTrajectory.of_sandwich`: the same with the hypothesis as a sandwich:
  `J t x` lies between the currents of two box members, up to `εm`.
* `IsTrajectory.of_static_sandwich`: the checkable form of the obligation, for
  a model `J x y` that is a function of the input voltage and the node voltage
  only, and an explicit set `U` of input values. The sandwich is required for
  `x ∈ U` and `y` in the safe domain, and the input waveform is required to
  stay in `U`.
* `IsTrajectory.of_feedthrough`: the node equation with the displacement
  currents through a gate-drain capacitance `CM` and one coupling capacitance
  `Cc` written out. Its solutions are trajectories when
  `CM * Su + Cc * Sg + εw ≤ eps`, where `Su` and `Sg` bound the slew of the
  input and of the aggressor. This is the formal place where an input slew
  bound is needed.

So a model whose current is multiplicatively off from one square law (the
typical shape of model-form error) is covered when the parameter box is wide
enough to sandwich it; the additive `eps` only has to absorb what the box does
not, such as conduction below threshold.

## What these statements do not give

1. **No existence for the other model.** The lemmas are about solutions of the
   other description, if there are any. Existence of solutions is proved in
   this repository only for the square law with constant parameters and a
   disturbance that is continuous in time (`exists_solution`, and
   `exists_trajectory_step` for one jump of the input). For another current
   law `J` it needs its own argument. The equation with feedthrough terms is
   covered by `exists_solution` only when `CM * du + Cc * dg + w` is a
   continuous function of time, which a ramp input with corners does not give.
2. **The obligation ranges over the input values that occur.** In
   `of_model_error` and `of_sandwich` the hypothesis is indexed by time and has
   to hold for the input value `u t` of each instant. The input classes of the
   guarantee do not bound the input (`u ≤ VIL` has no lower bound, `VIH ≤ u`
   no upper bound), so nothing limits the set of input values over which the
   two descriptions must be compared. Use the static form
   `of_static_sandwich`: the set `U` of input values is explicit there, the
   comparison is a statement about `U` and the safe domain alone, and the
   restriction of the input to `U` is a visible hypothesis.
3. **Where all box members coincide, the other model must agree in absolute
   terms.** The sandwich is as wide as the spread of the currents over the box,
   and no wider. Two cases, with the numbers of the illustrative record
   (`Vtnlo = 0.45`, `VDDhi - Vtplo = 1.53`):
   * At a grounded node, `y = 0`, and inputs `x ≥ 1.53`, the net current of
     every box member is exactly zero (the PMOS is cut off, `Ip_cutoff`, and
     the NMOS carries no current at zero drain-source voltage). The sandwich
     there says `|J x 0| ≤ εm`; the box contributes nothing.
   * For inputs `x ≤ 0.45` and a node at or above ground, the NMOS current of
     every box member is exactly zero (`In_cutoff`), so no box member conducts
     below threshold. The lower side of the sandwich then reads
     `Ip θ₁ x y - εm ≤ J x y` for some box member `θ₁`: what the NMOS of the
     other model conducts there has to fit between that model's PMOS current
     and the smallest PMOS current of the box, or into `εm`. Conduction below
     threshold at a valid-low input (`VIL = 0.40`) is the case in point.

These are statements about mathematics only. Whether a physical inverter, or a
SPICE model of one, satisfies the sandwich hypothesis, the slew bounds or the
capacitance bounds is an empirical question that this repository does not
settle. See `docs/assumptions.md`.

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

/-- **Static sandwich: the checkable form of the model-error obligation.** Let
`J x y` be the net current of another description of the node, as a function
of the input voltage `x` and the node voltage `y` only, and let `U` be an
explicit set of input values. If for every `x ∈ U` and every `y` in the safe
domain `J x y` lies between the net currents of two box members, up to `εm`,
and the input waveform stays in `U`, then every solution of
`c * v' = J (u t) (v t) + w t` with `c ∈ [Clo, Chi]`, `|w| ≤ εw` and
`εm + εw ≤ eps` is a trajectory.

The comparison hypothesis `hJ` mentions neither time nor the waveform. It is a
statement about two current laws on `U` and the safe domain. The price is the
visible hypothesis `hU` that the input never leaves `U`; the input classes of
the guarantee (`u ≤ VIL`, `VIH ≤ u`) do not provide it. -/
theorem IsTrajectory.of_static_sandwich {D : Design} {u v : ℝ → ℝ} {a b : ℝ}
    {J : ℝ → ℝ → ℝ} {U : Set ℝ} {w : ℝ → ℝ} {εm εw : ℝ} (hεm : 0 ≤ εm)
    (hbudget : εm + εw ≤ D.eps)
    (hU : ∀ t ∈ Ico a b, u t ∈ U)
    (hJ : ∀ x ∈ U, ∀ y ∈ D.Safe, ∃ θ₁ θ₂ : Params, D.InBox θ₁ ∧ D.InBox θ₂ ∧
      Inet θ₁ x y - εm ≤ J x y ∧ J x y ≤ Inet θ₂ x y + εm)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ εw)
    (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      D.Clo ≤ c ∧ c ≤ D.Chi ∧ c * v' = J (u t) (v t) + w t) :
    IsTrajectory D u v a b :=
  IsTrajectory.of_sandwich (J := fun t y => J (u t) y) hεm hbudget
    (fun t ht y hy => hJ (u t) (hU t ht) y hy) hw hcont hode

/-- **Feedthrough and coupling: where an input slew bound is needed.** The
output node of an inverter is coupled to its input through the gate-drain
capacitance `CM`, and to a neighbouring (aggressor) node `g` through a coupling
capacitance `Cc`. The node equation then reads

`c * v' = Inet θ (u t) (v t) + CM * du t + Cc * dg t + w t`,

where `du t` and `dg t` are the right derivatives of the input and of the
aggressor, and `w` collects whatever else flows into the node. Here `c` is the
*total* incremental capacitance of the node: it includes `CM` and `Cc` as well
as the load, and it is this total that has to lie in `[Clo, Chi]`.

If the slews are bounded, `|du| ≤ Su` and `|dg| ≤ Sg`, the residual is bounded,
`|w| ≤ εw`, and the budget `CM * Su + Cc * Sg + εw ≤ eps` holds, then every
solution is a trajectory, and the guarantee applies to it.

This lemma is the formal place where an input slew bound is needed. The
guarantee itself takes every input function; over that class the term
`CM * du` has no bound, so the feedthrough current is covered by `eps` only
under a slew bound such as `Su`.

It is a statement about the model, not evidence about a device. Whether a
device has a gate-drain capacitance of at most `CM`, whether its input and its
neighbours respect the slew bounds, and whether one aggressor behind a linear
capacitor describes its surroundings, is not addressed here.

The hypotheses `_hu` and `_hg` are not used by the proof: they say what `du`
and `dg` are, and the proof needs only the bounds on them. -/
theorem IsTrajectory.of_feedthrough {D : Design} {θ : Params} {u g v du dg w : ℝ → ℝ}
    {a b : ℝ} {CM Cc Su Sg εw : ℝ} (hCM : 0 ≤ CM) (hCc : 0 ≤ Cc)
    (hbudget : CM * Su + Cc * Sg + εw ≤ D.eps) (hθ : D.InBox θ)
    (_hu : ∀ t ∈ Ico a b, HasDerivWithinAt u (du t) (Ici t) t)
    (_hg : ∀ t ∈ Ico a b, HasDerivWithinAt g (dg t) (Ici t) t)
    (hSu : ∀ t ∈ Ico a b, |du t| ≤ Su) (hSg : ∀ t ∈ Ico a b, |dg t| ≤ Sg)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ εw)
    (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      D.Clo ≤ c ∧ c ≤ D.Chi ∧
      c * v' = Inet θ (u t) (v t) + CM * du t + Cc * dg t + w t) :
    IsTrajectory D u v a b where
  cont := hcont
  incl := fun t ht => by
    obtain ⟨v', c, hd, hc1, hc2, he⟩ := hode t ht
    refine ⟨v', c, hd, hc1, hc2, fun _ => ⟨θ, hθ, ?_⟩⟩
    have e : c * v' - Inet θ (u t) (v t) = CM * du t + Cc * dg t + w t := by
      rw [he]; ring
    have h1 : |CM * du t| ≤ CM * Su := by
      rw [abs_mul, abs_of_nonneg hCM]
      exact mul_le_mul_of_nonneg_left (hSu t ht) hCM
    have h2 : |Cc * dg t| ≤ Cc * Sg := by
      rw [abs_mul, abs_of_nonneg hCc]
      exact mul_le_mul_of_nonneg_left (hSg t ht) hCc
    have h3 := hw t ht
    have h4 := abs_add_le (CM * du t + Cc * dg t) (w t)
    have h5 := abs_add_le (CM * du t) (Cc * dg t)
    rw [e]
    linarith

end VoltageToBit
