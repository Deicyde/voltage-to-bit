import VoltageToBit.Examples.Illustrative
import VoltageToBit.Proofs.Concat
import VoltageToBit.Proofs.Contamination

/-!
# The input class of the guarantee: where it has instances

`illustrative_guarantee` and the general theorems `IsTrajectory.safe`, `.rise`,
`.fall`, `.decoded` are stated for every input function `u : ℝ → ℝ` and every
trajectory `v` for that input that starts in the safe domain. Such a statement
says something about an input on an interval only if a trajectory from the
safe domain exists for it there. This file shows, with compiled statements
about the illustrative record, that this is a real restriction.

Two inputs that differ at a single instant:

* `uStepL` is 1.8 V for `t ≤ 4` and 0 V afterwards. At the jump instant `t = 4`
  it still has its **old** value.
  `stepL_no_trajectory`: there is **no** trajectory for it on `[0, 10]` from
  any initial state in the safe domain. So for this input the hypotheses of
  the guarantee cannot be met with `a = 0` and `b = 10`: there the guarantee
  holds vacuously and says nothing.
* `uStepR` is 1.8 V for `t < 4` and 0 V from `t = 4` on. At the jump instant it
  already has its **new** value.
  `stepR_has_trajectory`: trajectories exist on `[0, 10]` from every initial
  state in the safe domain (the library's `exists_trajectory_step`), and for
  them the guarantee has content.

`step_input_scope` states both facts, and that the two inputs agree at every
`t ≠ 4`, in one statement with explicit numbers.

Two qualifiers are part of the non-existence statements and cannot be dropped.

* *From an initial state in the safe domain.* `IsTrajectory` asks for the
  current balance only while the node is in the safe domain. A constant
  outside it, 5 V for example, is therefore a trajectory for every input,
  `uStepL` included. The guarantee does not speak about such functions,
  because it assumes a start in the safe domain.
* *On `[0, 10]`.* On an interval that begins after the jump, `[5, 10]` for
  example, `uStepL` is constant, and trajectories exist from every state of
  the safe domain (`illustrative_exists_const` and
  `IsTrajectory.congr_input`).

Both inputs take only the values 1.8 V and 0 V, so each of them is a valid
input bit at every instant. That `uStepL` has no trajectory on `[0, 10]` from
the safe domain is not caused by an input in the undefined band.

## Why there is no trajectory from the safe domain

`IsTrajectory` asks, at every instant, for a right derivative and, while the
node is in the safe domain, for the current balance with the input value *at
that instant*. A trajectory that starts in the safe domain stays in it
(`IsTrajectory.safe`), so for it the balance is in force at every instant. At
`t = 4` the balance for `uStepL` refers to 1.8 V. For a node in
`[-0.02, 0.25]` V every parameter point of the box then allows a right
derivative of at most 1.72 V/ns (`Inet_high_le`: at most 6.6 µA, plus the 2 µA
allowance, into at least 5 fF). Immediately after `t = 4` the input is 0 V,
and while the node is at or below 0.45 V, which it is for the next 2 ps, every
parameter point forces a right derivative of at least 1.98 V/ns
(`Inet_low_ge`: at least 41.616 µA, less 2 µA, into at most 20 fF). A right
derivative cannot be smaller than a lower bound that holds immediately
afterwards (`rderiv_ge_of_right_nhd`), so no trajectory that starts in the
safe domain passes through such a point
(`no_trajectory_through_left_continuous_jump`). `stepL_no_trajectory` adds the
global part: whatever the initial state in the safe domain, at `t = 4` the
output is in `[-0.02, 0.25]` V.

`spike_no_trajectory` is the same obstruction for the input that is 0 V except
at the single instant `t = 0`, where it is 1.8 V: no trajectory on `[0, 10]`
starts with an output in `[-0.02, 0.25]` V, although for the constant input
0 V trajectories exist from every state of the safe domain
(`illustrative_exists_const`).

## What this delimits

The guarantee quantifies over all input functions, but it has instances only
where trajectories from the safe domain exist.

* `exists_trajectory` proves existence for continuous inputs (only the input
  values on `[a, b)` matter, `IsTrajectory.congr_input`), and
  `exists_trajectory_step` for an input with one jump that takes its new value
  at the jump instant. Both give a trajectory from every initial state in the
  safe domain, and both assume constant parameters in the box, a Lipschitz
  capacitance in range and a continuous disturbance within the bound, which
  serve only to build the trajectory.
* For `uStepL` on `[0, 10]`, non-existence from an initial state in the safe
  domain is proved here.
* For an input that no existence theorem reaches, the guarantee is a statement
  about whatever trajectories from the safe domain there are, possibly none.

The obstruction belongs to the pointwise trajectory notion, not to a circuit:
the two step inputs differ at one instant only. It is proved here for one jump
of the illustrative record (from 1.8 V to 0 V, with the node in
`[-0.02, 0.25]` V) and, for `uStepL`, on the interval `[0, 10]`; nothing is
stated here about other jumps or other states, or about `uStepL` on other
intervals. An ideal digital edge has instances in this model when it takes its
new value at the jump instant.

## A step and its right derivative

`uStepR_hasDerivWithinAt_zero`, `uStepR_not_continuousOn`: the ideal edge
`uStepR` has right derivative zero at every instant, the jump instant
included, and it is not continuous. So a bound on the right derivative of an
input is not a slew bound unless the input is also continuous.

Provenance. The content of this file was contributed by workstream E's review
probes (`review/D01_JumpInput_PerInstant.lean`, with
`review/P01_JumpInputVacuity.lean` and
`review/P02_RightContinuousStepExists.lean` behind it; findings E1-01 and E2-01
of `docs/adversarial-review.md`) and ported into the library. Added in the
port: `step_input_scope`. `uStepL_eq_uStepR_of_ne` restates
`uStepR_eq_off_jump` of P02, and `illustrative_box_bounds` is `box_bounds` of
D01 under a more specific name. Added later: the two statements about the
right derivative of `uStepR`.
-/

namespace VoltageToBit.Examples

open Set Filter
open scoped Topology

/-! ## A right derivative cannot jump upwards -/

/-- Real-analysis core. If `v` is continuous on `[t0, t0 + δ]` and its right
derivative is at least `m` at every point of the **open** interval
`(t0, t0 + δ)`, then its right derivative at `t0`, if it exists, is at least
`m` as well. (A right derivative cannot jump upwards immediately after `t0`.) -/
theorem rderiv_ge_of_right_nhd {v : ℝ → ℝ} {t0 δ m d0 : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn v (Icc t0 (t0 + δ)))
    (h0 : HasDerivWithinAt v d0 (Ici t0) t0)
    (hder : ∀ t ∈ Ioo t0 (t0 + δ), ∃ d, HasDerivWithinAt v d (Ici t) t ∧ m ≤ d) :
    m ≤ d0 := by
  -- Step 1: `v t0 + m * (z - t0) ≤ v z` for every `z` just after `t0`.
  have key : ∀ z ∈ Ioo t0 (t0 + δ), v t0 + m * (z - t0) ≤ v z := by
    intro z hz
    have h1 : ∀ t1 ∈ Ioo t0 z, v t1 + m * (z - t1) ≤ v z := by
      intro t1 ht1
      have hsub : Icc t1 z ⊆ Icc t0 (t0 + δ) := Icc_subset_Icc ht1.1.le hz.2.le
      have hsubo : Ico t1 z ⊆ Ioo t0 (t0 + δ) :=
        fun x hx => ⟨lt_of_lt_of_le ht1.1 hx.1, lt_trans hx.2 hz.2⟩
      have hd : ∀ x ∈ Ico t1 z, HasDerivWithinAt v (derivWithin v (Ici x) x) (Ici x) x := by
        intro x hx
        obtain ⟨d, hd, -⟩ := hder x (hsubo hx)
        exact hd.differentiableWithinAt.hasDerivWithinAt
      have hbound : ∀ x ∈ Ico t1 z, m ≤ derivWithin v (Ici x) x := by
        intro x hx
        obtain ⟨d, hd, hm⟩ := hder x (hsubo hx)
        rw [hd.derivWithin (uniqueDiffWithinAt_Ici x)]
        exact hm
      have := image_le_of_deriv_right_le_deriv_boundary
        (f := fun s => v t1 + m * (s - t1)) (f' := fun _ => m) (a := t1) (b := z)
        (by fun_prop)
        (fun x _ => by
          have h := (((hasDerivAt_id x).sub_const t1).const_mul m).const_add (v t1)
          simpa using h.hasDerivWithinAt)
        (B := v) (B' := fun x => derivWithin v (Ici x) x) (by simp) (hcont.mono hsub) hd hbound
        (x := z) ⟨ht1.2.le, le_rfl⟩
      simpa using this
    have hcw : ContinuousWithinAt v (Ioi t0) t0 := by
      have h2 : ContinuousWithinAt v (Icc t0 (t0 + δ)) t0 := hcont t0 ⟨le_rfl, by linarith⟩
      exact h2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem ⟨le_rfl, by linarith⟩)
    have htend : Tendsto (fun t1 => v t1 + m * (z - t1)) (𝓝[>] t0) (𝓝 (v t0 + m * (z - t0))) := by
      have h2 : Tendsto (fun t1 : ℝ => m * (z - t1)) (𝓝[>] t0) (𝓝 (m * (z - t0))) :=
        ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto t0).mono_left
          nhdsWithin_le_nhds
      exact hcw.tendsto.add h2
    have hev : ∀ᶠ t1 in 𝓝[>] t0, v t1 + m * (z - t1) ≤ v z := by
      filter_upwards [Ioo_mem_nhdsGT hz.1] with t1 ht1 using h1 t1 ht1
    exact le_of_tendsto htend hev
  -- Step 2: the slope from `t0` is at least `m` just after `t0`, and tends to `d0`.
  have hslope : Tendsto (slope v t0) (𝓝[>] t0) (𝓝 d0) := by
    have := hasDerivWithinAt_iff_tendsto_slope.mp h0
    rwa [Ici_sdiff_left] at this
  have hev : ∀ᶠ z in 𝓝[>] t0, m ≤ slope v t0 z := by
    filter_upwards [Ioo_mem_nhdsGT (show t0 < t0 + δ by linarith)] with z hz
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hz.1)]
    linarith [key z hz]
  exact ge_of_tendsto hslope hev

/-! ## Bounds on the device current that hold for every point of the box -/

/-- The parameter box of the illustrative record, with its numbers. -/
theorem illustrative_box_bounds {θ : Params} (hθ : illustrative.InBox θ) :
    (1.62 ≤ θ.VDD ∧ θ.VDD ≤ 1.98) ∧ (160 ≤ θ.kn ∧ θ.kn ≤ 240) ∧ (80 ≤ θ.kp ∧ θ.kp ≤ 120) ∧
    (0.45 ≤ θ.Vtn ∧ θ.Vtn ≤ 0.60) ∧ (0.45 ≤ θ.Vtp ∧ θ.Vtp ≤ 0.60) :=
  ⟨⟨hθ.VDD_ge, hθ.VDD_le⟩, ⟨hθ.kn_ge, hθ.kn_le⟩, ⟨hθ.kp_ge, hθ.kp_le⟩,
    ⟨hθ.Vtn_ge, hθ.Vtn_le⟩, ⟨hθ.Vtp_ge, hθ.Vtp_le⟩⟩

/-- Input at 1.8 V, node in `[-0.02, 0.25]` V: no box member charges the node
with more than 6.6 µA. -/
theorem Inet_high_le {θ : Params} (hθ : illustrative.InBox θ) {x : ℝ} (h1 : -0.02 ≤ x)
    (h2 : x ≤ 0.25) : Inet θ 1.8 x ≤ 6.6 := by
  obtain ⟨⟨hV1, hV2⟩, ⟨hkn1, hkn2⟩, -, ⟨hn1, hn2⟩, ⟨hp1, -⟩⟩ := illustrative_box_bounds hθ
  have hp : Ip θ 1.8 x = 0 := Ip_cutoff (by linarith) (by linarith)
  rcases le_total 0 x with hx | hx
  · have := In_nonneg (θ := θ) (u := 1.8) (by linarith : (0 : ℝ) ≤ θ.kn) hx
    rw [Inet, hp]; linarith
  · have hn : In θ 1.8 x = -(θ.kn * ((1.8 - x - θ.Vtn) * (-x) - (-x) ^ 2 / 2)) :=
      In_rev_triode hx (by linarith)
    rw [Inet, hp, hn]
    have ha : 0 ≤ -x := by linarith
    have hc : (1.8 - x - θ.Vtn) * (-x) - (-x) ^ 2 / 2 ≤ 0.0274 := by nlinarith
    have hc0 : 0 ≤ (1.8 - x - θ.Vtn) * (-x) - (-x) ^ 2 / 2 := by nlinarith
    nlinarith

/-- Input at 1.8 V, node at or below -0.02 V: every box member charges the node
with at least 3.8 µA (reverse conduction of the NMOS). -/
theorem Inet_high_ge {θ : Params} (hθ : illustrative.InBox θ) {x : ℝ}
    (h2 : x ≤ -0.02) : 3.8 ≤ Inet θ 1.8 x := by
  obtain ⟨⟨hV1, hV2⟩, ⟨hkn1, hkn2⟩, -, ⟨hn1, hn2⟩, ⟨hp1, -⟩⟩ := illustrative_box_bounds hθ
  have hp : Ip θ 1.8 x = 0 := Ip_cutoff (by linarith) (by linarith)
  have hn : In θ 1.8 x = -(θ.kn * ((1.8 - x - θ.Vtn) * (-x) - (-x) ^ 2 / 2)) :=
    In_rev_triode (by linarith) (by linarith)
  rw [Inet, hp, hn]
  have hc : 0.0242 ≤ (1.8 - x - θ.Vtn) * (-x) - (-x) ^ 2 / 2 := by nlinarith
  nlinarith

/-- Input at 0 V, node in `[-0.10, 0.45]` V: every box member charges the node
with at least 41.616 µA (PMOS saturated, NMOS off). -/
theorem Inet_low_ge {θ : Params} (hθ : illustrative.InBox θ) {x : ℝ} (h1 : -0.10 ≤ x)
    (h2 : x ≤ 0.45) : 41.616 ≤ Inet θ 0 x := by
  obtain ⟨⟨hV1, hV2⟩, -, ⟨hkp1, hkp2⟩, ⟨hn1, hn2⟩, ⟨hp1, hp2⟩⟩ := illustrative_box_bounds hθ
  have hp : Ip θ 0 x = θ.kp / 2 * (θ.VDD - 0 - θ.Vtp) ^ 2 := Ip_sat (by linarith) (by linarith)
  have hn : In θ 0 x = 0 := by
    rcases le_total 0 x with hx | hx
    · exact In_cutoff (by linarith) hx
    · exact In_rev_cutoff hx (by linarith)
  rw [Inet, hp, hn]
  have hd : 1.02 ≤ θ.VDD - 0 - θ.Vtp := by linarith
  have hsq : 1.02 ^ 2 ≤ (θ.VDD - 0 - θ.Vtp) ^ 2 := by nlinarith
  nlinarith

/-! ## The local obstruction -/

/-- **Local obstruction.** If the input is 1.8 V at the instant `t0` and 0 V on
`(t0, t0 + 0.002)`, no trajectory of the illustrative record that starts in the
safe domain passes through `(t0, v t0)` with `v t0 ∈ [-0.02, 0.25]` V. Whatever
box points are used, the balance at `t0` caps the right derivative at
1.72 V/ns, while just after `t0` it must be at least 1.98 V/ns. -/
theorem no_trajectory_through_left_continuous_jump {u v : ℝ → ℝ} {a b t0 : ℝ}
    (h : IsTrajectory illustrative u v a b) (h0 : v a ∈ illustrative.Safe)
    (hat0 : a ≤ t0) (ht0b : t0 + 0.002 ≤ b)
    (hu0 : u t0 = 1.8) (hu1 : ∀ t ∈ Ioo t0 (t0 + 0.002), u t = 0)
    (hv1 : -0.02 ≤ v t0) (hv2 : v t0 ≤ 0.25) : False := by
  have hadm := illustrative_admissible
  have hsafe := h.safe hadm h0
  have hSafe : ∀ x : ℝ, x ∈ illustrative.Safe ↔ -0.10 ≤ x ∧ x ≤ 2.08 := by
    intro x; simp [Design.Safe, illustrative]
  have heps : illustrative.eps = 2 := by norm_num [illustrative]
  have ht0 : t0 ∈ Ico a b := ⟨hat0, by linarith⟩
  -- (1) upper bound for the right derivative at `t0`, whatever box point is used there
  have hr0 : rderiv v t0 ≤ 1.72 := by
    obtain ⟨c, hc1, hc2, hb⟩ := h.balance t0 ht0
    obtain ⟨θ, hθ, hb'⟩ := hb (hsafe t0 ⟨ht0.1, ht0.2.le⟩)
    rw [hu0, heps] at hb'
    have hI := Inet_high_le hθ hv1 hv2
    have hc1' : (5 : ℝ) ≤ c := by simpa [illustrative] using hc1
    have hup : c * rderiv v t0 ≤ 8.6 := by linarith [(abs_le.mp hb').2]
    by_contra hneg
    push Not at hneg
    have : (5 : ℝ) * rderiv v t0 ≤ c * rderiv v t0 :=
      mul_le_mul_of_nonneg_right hc1' (by linarith)
    linarith
  -- (2) the output is still below 0.45 V on `[t0, t0 + 0.002]`
  have hvle : ∀ t ∈ Icc t0 (t0 + 0.002), v t ≤ 0.45 := by
    intro t ht
    have hslope : (illustrative.IchargeMax 0 1.8 + illustrative.eps) / illustrative.Clo
        = 78.9508 := by
      norm_num [Design.IchargeMax, illustrative, psq_eq_ite]
    have hbound := h.rise_at_most hadm h0 (s := t0) (e := t0 + 0.002) (ulo := 0) (uhi := 1.8)
      (l := 0.25) hat0 ht0b ?_ hv2 t ht
    · rw [hslope] at hbound
      nlinarith [ht.1, ht.2]
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · rw [← hx0, hu0]; norm_num
      · rw [hu1 x ⟨hx0, hx.2⟩]; norm_num
  -- (3) lower bound for the right derivative just after `t0`, whatever box point is used
  have hr1 : ∀ t ∈ Ioo t0 (t0 + 0.002), ∃ d, HasDerivWithinAt v d (Ici t) t ∧ (1.98 : ℝ) ≤ d := by
    intro t ht
    have htab : t ∈ Ico a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨rderiv v t, h.hasDeriv t htab, ?_⟩
    obtain ⟨c, hc1, hc2, hb⟩ := h.balance t htab
    have hs := hsafe t ⟨htab.1, htab.2.le⟩
    obtain ⟨θ, hθ, hb'⟩ := hb hs
    have hlo : -0.10 ≤ v t := ((hSafe _).mp hs).1
    rw [hu1 t ht, heps] at hb'
    have hI := Inet_low_ge hθ hlo (hvle t ⟨ht.1.le, ht.2.le⟩)
    have hc2' : c ≤ 20 := by simpa [illustrative] using hc2
    have hc1' : (5 : ℝ) ≤ c := by simpa [illustrative] using hc1
    have hlow : (39.616 : ℝ) ≤ c * rderiv v t := by linarith [(abs_le.mp hb').1]
    have hpos : 0 < rderiv v t := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ c) (not_lt.mp hneg)
      linarith
    have : c * rderiv v t ≤ 20 * rderiv v t := mul_le_mul_of_nonneg_right hc2' hpos.le
    linarith
  -- (4) contradiction
  have hcont : ContinuousOn v (Icc t0 (t0 + 0.002)) := h.cont.mono (Icc_subset_Icc hat0 ht0b)
  have := rderiv_ge_of_right_nhd (by norm_num : (0 : ℝ) < 0.002) hcont (h.hasDeriv t0 ht0) hr1
  linarith

/-! ## Two step inputs that differ at one instant -/

/-- High (1.8 V) until `t = 4` **inclusive**, low (0 V) afterwards: at the jump
instant the input still has its old value. -/
noncomputable def uStepL (t : ℝ) : ℝ := if t ≤ 4 then 1.8 else 0

/-- High (1.8 V) until `t = 4` **exclusive**, low (0 V) from `t = 4` on: at the
jump instant the input already has its new value. -/
noncomputable def uStepR (t : ℝ) : ℝ := if t < 4 then 1.8 else 0

/-- The two step inputs differ only at the instant `t = 4`. -/
theorem uStepL_eq_uStepR_of_ne {t : ℝ} (ht : t ≠ 4) : uStepL t = uStepR t := by
  rcases lt_or_gt_of_ne ht with h | h
  · simp [uStepL, uStepR, h, h.le]
  · simp [uStepL, uStepR, not_lt.mpr h.le, not_le.mpr h]

/-- **No trajectory from the safe domain.** For the illustrative record and the
input `uStepL` there is no trajectory on `[0, 10]` from any initial state in
the safe domain. Both qualifiers are needed: a constant outside the safe
domain is a trajectory for every input, and on an interval that begins after
the jump `uStepL` is constant and trajectories from the safe domain exist. -/
theorem stepL_no_trajectory (v : ℝ → ℝ) (h : IsTrajectory illustrative uStepL v 0 10)
    (h0 : v 0 ∈ illustrative.Safe) : False := by
  have hadm := illustrative_admissible
  have hsafe := h.safe hadm h0
  have hSafe : ∀ x : ℝ, x ∈ illustrative.Safe ↔ -0.10 ≤ x ∧ x ≤ 2.08 := by
    intro x; simp [Design.Safe, illustrative]
  have heps : illustrative.eps = 2 := by norm_num [illustrative]
  -- input high on [0, 4): the output is valid-low at t = 4 ...
  have hv2 : v 4 ≤ 0.25 := by
    have := h.fall hadm h0 (s := 0) (e := 4) le_rfl (by norm_num)
      (fun t ht => by rw [uStepL, ite_eq_left ht.2.le]; norm_num [illustrative]) 4
      ⟨by norm_num, le_rfl⟩ (by linarith [illustrative_tauDn_le])
    simpa [illustrative] using this
  -- ... and it has recovered from any undershoot: v 4 ≥ -0.02
  have hv1 : -0.02 ≤ v 4 := by
    have hsub : Ico (0 : ℝ) 4 ⊆ Ico 0 10 := Ico_subset_Ico le_rfl (by norm_num)
    refine rise_by (v := v) (v' := rderiv v) (a := 0) (b := 4) (c := -0.02) (l := -0.10)
      (m := 0.09) (h.cont.mono (Icc_subset_Icc le_rfl (by norm_num)))
      (fun x hx => h.hasDeriv x (hsub hx)) (by norm_num) ((hSafe _).mp h0).1 ?_ 4
      ⟨by norm_num, le_rfl⟩ (by norm_num)
    intro t ht hvt
    obtain ⟨c, hc1, hc2, hb⟩ := h.balance t (hsub ht)
    have hs := hsafe t ⟨(hsub ht).1, (hsub ht).2.le⟩
    obtain ⟨θ, hθ, hb'⟩ := hb hs
    rw [uStepL, ite_eq_left ht.2.le, heps] at hb'
    have hI := Inet_high_ge hθ hvt
    have hc2' : c ≤ 20 := by simpa [illustrative] using hc2
    have hc1' : (5 : ℝ) ≤ c := by simpa [illustrative] using hc1
    have hlow : (1.8 : ℝ) ≤ c * rderiv v t := by linarith [(abs_le.mp hb').1]
    have hpos : 0 < rderiv v t := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ c) (not_lt.mp hneg)
      linarith
    have : c * rderiv v t ≤ 20 * rderiv v t := mul_le_mul_of_nonneg_right hc2' hpos.le
    linarith
  exact no_trajectory_through_left_continuous_jump h h0 (t0 := 4) (by norm_num) (by norm_num)
    (by rw [uStepL, ite_eq_left le_rfl])
    (fun t ht => by rw [uStepL, ite_eq_right (not_le.mpr ht.1)]) hv1 hv2

/-- **Trajectories exist for the twin input.** The library's existence theorem
for a step covers `uStepR`, which takes its new value at `t = 4`: trajectories
exist on `[0, 10]` from every initial state in the safe domain. (The proof
builds them with nominal parameters, capacitance 10 fF and zero disturbance;
the statement does not name these data.) -/
theorem stepR_has_trajectory (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧ IsTrajectory illustrative uStepR v 0 10 :=
  exists_trajectory_step illustrative_admissible nominal_inBox (Cf := fun _ => 10) (Kc := 0)
    (fun _ => by norm_num [illustrative]) (fun x _ y _ => by simp)
    (u₁ := fun _ => 1.8) (u₂ := fun _ => 0) (w := fun _ => 0)
    continuous_const continuous_const continuous_const (a := 0) (c := 4) (b := 10)
    (by norm_num) (by norm_num) (fun t _ => by norm_num [illustrative]) hv₀

/-- **Scope of the guarantee, in one statement.** Two inputs that are 1.8 V
before `t = 4` and 0 V after it, and differ only in the value they take at the
instant `t = 4`:

1. they agree at every other instant;
2. for the one that keeps its old value at the jump instant there is no
   trajectory of the illustrative record on `[0, 10]` from any initial state in
   `[-0.10, 2.08]` V, so the hypotheses of `illustrative_guarantee` cannot be
   met with `a = 0` and `b = 10`, and there the guarantee says nothing;
3. for the one that takes its new value at the jump instant a trajectory on
   `[0, 10]` exists from every initial state in `[-0.10, 2.08]` V. -/
theorem step_input_scope :
    (uStepL 4 = 1.8 ∧ uStepR 4 = 0 ∧ ∀ t : ℝ, t ≠ 4 → uStepL t = uStepR t) ∧
    (¬ ∃ v : ℝ → ℝ, v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧ IsTrajectory illustrative uStepL v 0 10) ∧
    (∀ v₀ ∈ Icc (-0.10 : ℝ) 2.08,
      ∃ v : ℝ → ℝ, v 0 = v₀ ∧ IsTrajectory illustrative uStepR v 0 10) := by
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  refine ⟨⟨by simp [uStepL], by simp [uStepR], fun t ht => uStepL_eq_uStepR_of_ne ht⟩, ?_,
    fun v₀ hv₀ => stepR_has_trajectory v₀ (by rw [hsafe]; exact hv₀)⟩
  rintro ⟨v, h0, h⟩
  exact stepL_no_trajectory v h (by rw [hsafe]; exact h0)

/-! ## A step and its right derivative -/

/-- **The ideal step has right derivative zero at every instant**, the jump
instant `t = 4` included: just after any instant `uStepR` is constant. So a
bound on the right derivative of an input is not a slew bound unless the input
is also continuous. `uStepR` swings by 1.8 V in no time, it meets the bound
zero, and it is not continuous (`uStepR_not_continuousOn`). This is why the
charge-balance lemma in `Proofs/ModelError.lean` assumes a continuous input. -/
theorem uStepR_hasDerivWithinAt_zero : ∀ t : ℝ, HasDerivWithinAt uStepR 0 (Ici t) t := by
  intro t
  rcases lt_or_ge t 4 with ht | ht
  · -- just after an instant `t < 4` the input is still 1.8 V
    refine (hasDerivWithinAt_const t (Ici t) (1.8 : ℝ)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ico_mem_nhdsGE ht] with x hx
      simp [uStepR, hx.2]
    · simp [uStepR, ht]
  · -- from an instant `t ≥ 4` on the input is 0 V
    refine (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr ?_ ?_
    · intro x hx
      simp [uStepR, not_lt.mpr (le_trans ht hx)]
    · simp [uStepR, not_lt.mpr ht]

/-- **The ideal step is not continuous on `[0, 10]`.** It is 1.8 V at `t = 0`
and 0 V at `t = 10` and takes no value in between. Together with
`uStepR_hasDerivWithinAt_zero`: a function whose right derivative is zero at
every instant need not be constant, so a bound on the right derivative alone
does not bound how fast an input changes. -/
theorem uStepR_not_continuousOn : ¬ ContinuousOn uStepR (Icc (0 : ℝ) 10) := by
  intro h
  -- a continuous function on `[0, 10]` that is 1.8 at 0 and 0 at 10 takes the value 1
  have h0 : uStepR 0 = 1.8 := by simp [uStepR]
  have h10 : uStepR 10 = 0 := by norm_num [uStepR]
  have hmem : (1 : ℝ) ∈ Icc (uStepR 10) (uStepR 0) := by
    rw [h0, h10]; constructor <;> norm_num
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 10) h hmem
  unfold uStepR at ht
  split_ifs at ht <;> norm_num at ht

/-! ## A single-instant change of the input -/

/-- The constant-low input, changed at the single instant `t = 0`. -/
noncomputable def uSpike (t : ℝ) : ℝ := if t = 0 then 1.8 else 0

/-- For `uSpike`, which differs from the constant input 0 V only at the instant
`t = 0`, no trajectory of the illustrative record on `[0, 10]` starts with an
output in `[-0.02, 0.25]` V. (For the constant input 0 V trajectories exist from
every state of the safe domain, by `illustrative_exists_const`.) -/
theorem spike_no_trajectory (v : ℝ → ℝ) (h : IsTrajectory illustrative uSpike v 0 10)
    (h1 : -0.02 ≤ v 0) (h2 : v 0 ≤ 0.25) : False := by
  have h0 : v 0 ∈ illustrative.Safe := by
    simp only [Design.Safe, illustrative, mem_Icc]
    constructor <;> linarith
  exact no_trajectory_through_left_continuous_jump h h0 (t0 := 0) le_rfl (by norm_num)
    (by simp [uSpike])
    (fun t ht => by
      have : t ≠ 0 := ne_of_gt ht.1
      simp [uSpike, this]) h1 h2

end VoltageToBit.Examples
