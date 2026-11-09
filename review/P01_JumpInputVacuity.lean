import VoltageToBit

/-!
# Probe P01 (workstream E): inputs with a left-continuous jump have NO trajectories

The universal guarantee is advertised for "every input `u : ℝ → ℝ` (no
regularity assumed)" (`Proofs/Guarantee.lean`, `docs/interface.md` §1, §4).
`IsTrajectory` asks for a right derivative satisfying the current balance at
**every** instant, with the input value **at** that instant. This probe shows
what that means for an input that jumps and takes its pre-jump value at the
jump instant:

* `uStepL` is `1.8 V` for `t ≤ 4` and `0 V` for `t > 4`. It decodes to a valid
  bit at every instant (`uStepL_valid_high`, `uStepL_valid_low`).
* `stepL_no_trajectory`: for the illustrative design and nominal parameters
  there is **no** trajectory on `[0, 10]` for this input from **any** initial
  state in the safe domain. The hypothesis set of `illustrative_guarantee` is
  unsatisfiable for this input, so the guarantee is vacuous there
  (`stepL_guarantee_proves_anything`).
* `spike_no_trajectory` / `const_low_has_trajectory`: changing the constant-low
  input at the single instant `t = 0` destroys every trajectory that starts
  with a valid-low output, although the two inputs agree at all other times.

Nothing here contradicts a theorem of the library. It delimits the regime in
which the universally quantified guarantee has any instances.
-/

open Set Filter Topology
open VoltageToBit VoltageToBit.Examples

namespace Review.P01

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

/-! ## The nominal device current for the two input values -/

/-- Nominal net current with the input at `1.8 V` (NMOS on, PMOS off). -/
theorem Inet_nominal_high {x : ℝ} (hx : x ≤ 1.3) :
    Inet nominal 1.8 x = 100 * (x ^ 2 - 2.6 * x) := by
  have h1 : psq ((1.8 : ℝ) - 1.8 - 0.5) = 0 := psq_of_nonpos (by norm_num)
  have h2 : psq (x - 1.8 - 0.5) = 0 := psq_of_nonpos (by linarith)
  have h3 : psq ((1.8 : ℝ) - 0.5) = (1.8 - 0.5) ^ 2 := psq_of_nonneg (by norm_num)
  have h4 : psq ((1.8 : ℝ) - x - 0.5) = (1.8 - x - 0.5) ^ 2 := psq_of_nonneg (by linarith)
  simp only [Inet, Ip, In, nominal, h1, h2, h3, h4]
  ring

/-- Nominal net current with the input at `0 V` (PMOS saturated, NMOS off). -/
theorem Inet_nominal_low {x : ℝ} (hx1 : -0.5 ≤ x) (hx2 : x ≤ 0.5) :
    Inet nominal 0 x = 84.5 := by
  have h1 : psq ((1.8 : ℝ) - 0 - 0.5) = (1.8 - 0 - 0.5) ^ 2 := psq_of_nonneg (by norm_num)
  have h2 : psq (x - 0 - 0.5) = 0 := psq_of_nonpos (by linarith)
  have h3 : psq ((0 : ℝ) - 0.5) = 0 := psq_of_nonpos (by norm_num)
  have h4 : psq ((0 : ℝ) - x - 0.5) = 0 := psq_of_nonpos (by linarith)
  simp only [Inet, Ip, In, nominal, h1, h2, h3, h4]
  norm_num

/-- **Local obstruction.** Illustrative design, nominal parameters. If the
input is `1.8 V` at the instant `t0` and `0 V` on `(t0, t0 + 0.003)`, no
trajectory can pass through `(t0, v t0)` with `v t0 ∈ [-0.06, 0.25]`: the
balance at `t0` caps the right derivative at `3.592 V/ns`, while the balance
just after `t0` forces it to be at least `4.125 V/ns`. -/
theorem no_trajectory_through_left_continuous_jump {u v : ℝ → ℝ} {a b t0 : ℝ}
    (h : IsTrajectory illustrative nominal u v a b) (h0 : v a ∈ illustrative.Safe)
    (hat0 : a ≤ t0) (ht0b : t0 + 0.003 ≤ b)
    (hu0 : u t0 = 1.8) (hu1 : ∀ t ∈ Ioo t0 (t0 + 0.003), u t = 0)
    (hv1 : -0.06 ≤ v t0) (hv2 : v t0 ≤ 0.25) : False := by
  have hadm := illustrative_admissible
  have hθ := nominal_inBox
  have hsafe := h.safe hadm hθ h0
  have hSafe : ∀ x : ℝ, x ∈ illustrative.Safe ↔ -0.10 ≤ x ∧ x ≤ 2.08 := by
    intro x; simp [Design.Safe, illustrative]
  -- (1) upper bound for the right derivative at `t0`
  have ht0 : t0 ∈ Ico a b := ⟨hat0, by linarith⟩
  have hr0 : rderiv v t0 ≤ 3.592 := by
    obtain ⟨c, hc1, hc2, hb⟩ := h.balance t0 ht0
    have hb' := hb (hsafe t0 ⟨ht0.1, ht0.2.le⟩)
    rw [hu0, Inet_nominal_high (by linarith)] at hb'
    have hc1' : (5 : ℝ) ≤ c := by simpa [illustrative] using hc1
    have heps : illustrative.eps = 2 := by norm_num [illustrative]
    rw [heps] at hb'
    have hI : 100 * ((v t0) ^ 2 - 2.6 * v t0) ≤ 15.96 := by nlinarith
    have hup : c * rderiv v t0 ≤ 17.96 := by linarith [(abs_le.mp hb').2]
    by_contra hneg
    push Not at hneg
    have : (5 : ℝ) * rderiv v t0 ≤ c * rderiv v t0 :=
      mul_le_mul_of_nonneg_right hc1' (by linarith)
    linarith
  -- (2) the output is still below 0.5 V on `[t0, t0 + 0.003]`
  have hvle : ∀ t ∈ Icc t0 (t0 + 0.003), v t ≤ 0.5 := by
    intro t ht
    have hslope : (illustrative.IchargeMax 0 1.8 + illustrative.eps) / illustrative.Clo
        = 78.9508 := by
      norm_num [Design.IchargeMax, illustrative, psq_eq_ite]
    have hbound := h.rise_at_most hadm hθ h0 (s := t0) (e := t0 + 0.003) (ulo := 0) (uhi := 1.8)
      (l := 0.25) hat0 ht0b ?_ hv2 t ht
    · rw [hslope] at hbound
      nlinarith [ht.1, ht.2]
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · rw [← hx0, hu0]; norm_num
      · rw [hu1 x ⟨hx0, hx.2⟩]; norm_num
  -- (3) lower bound for the right derivative just after `t0`
  have hr1 : ∀ t ∈ Ioo t0 (t0 + 0.003), ∃ d, HasDerivWithinAt v d (Ici t) t ∧ (4.125 : ℝ) ≤ d := by
    intro t ht
    have htab : t ∈ Ico a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨rderiv v t, h.hasDeriv t htab, ?_⟩
    obtain ⟨c, hc1, hc2, hb⟩ := h.balance t htab
    have hs := hsafe t ⟨htab.1, htab.2.le⟩
    have hb' := hb hs
    have hlo : -0.10 ≤ v t := ((hSafe _).mp hs).1
    rw [hu1 t ht, Inet_nominal_low (by linarith) (hvle t ⟨ht.1.le, ht.2.le⟩)] at hb'
    have hc2' : c ≤ 20 := by simpa [illustrative] using hc2
    have hc1' : (5 : ℝ) ≤ c := by simpa [illustrative] using hc1
    have heps : illustrative.eps = 2 := by norm_num [illustrative]
    rw [heps] at hb'
    have hlow : (82.5 : ℝ) ≤ c * rderiv v t := by linarith [(abs_le.mp hb').1]
    have hpos : 0 < rderiv v t := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ c) (not_lt.mp hneg)
      linarith
    have : c * rderiv v t ≤ 20 * rderiv v t := mul_le_mul_of_nonneg_right hc2' hpos.le
    linarith
  -- (4) contradiction
  have hcont : ContinuousOn v (Icc t0 (t0 + 0.003)) := h.cont.mono (Icc_subset_Icc hat0 ht0b)
  have := rderiv_ge_of_right_nhd (by norm_num : (0 : ℝ) < 0.003) hcont (h.hasDeriv t0 ht0) hr1
  linarith

/-! ## A step input that is valid at every instant but has no trajectory -/

/-- High until `t = 4` **inclusive**, low afterwards. -/
noncomputable def uStepL (t : ℝ) : ℝ := if t ≤ 4 then 1.8 else 0

theorem uStepL_valid_high {t : ℝ} (ht : t ≤ 4) : illustrative.decodeIn (uStepL t) = some true := by
  have hio : illustrative.VIL < illustrative.VIH := by norm_num [illustrative]
  rw [Design.decodeIn, decode_eq_true_iff hio, uStepL, ite_eq_left ht]
  norm_num [illustrative]

theorem uStepL_valid_low {t : ℝ} (ht : 4 < t) : illustrative.decodeIn (uStepL t) = some false := by
  rw [Design.decodeIn, decode_eq_false_iff, uStepL, ite_eq_right (not_le.mpr ht)]
  norm_num [illustrative]

/-- **No trajectory at all.** For the illustrative design with nominal
parameters and the input `uStepL`, there is no trajectory on `[0, 10]` from any
initial state in the safe domain. -/
theorem stepL_no_trajectory (v : ℝ → ℝ) (h : IsTrajectory illustrative nominal uStepL v 0 10)
    (h0 : v 0 ∈ illustrative.Safe) : False := by
  have hadm := illustrative_admissible
  have hθ := nominal_inBox
  have hsafe := h.safe hadm hθ h0
  have hSafe : ∀ x : ℝ, x ∈ illustrative.Safe ↔ -0.10 ≤ x ∧ x ≤ 2.08 := by
    intro x; simp [Design.Safe, illustrative]
  -- input high on [0, 4): the output is valid-low at t = 4 ...
  have hv2 : v 4 ≤ 0.25 := by
    have := h.fall hadm hθ h0 (s := 0) (e := 4) le_rfl (by norm_num)
      (fun t ht => by rw [uStepL, ite_eq_left ht.2.le]; norm_num [illustrative]) 4
      ⟨by norm_num, le_rfl⟩ (by linarith [illustrative_tauDn_le])
    simpa [illustrative] using this
  -- ... and it has recovered from any undershoot: v 4 ≥ -0.06
  have hv1 : -0.06 ≤ v 4 := by
    have hsub : Ico (0 : ℝ) 4 ⊆ Ico 0 10 := Ico_subset_Ico le_rfl (by norm_num)
    refine rise_by (v := v) (v' := rderiv v) (a := 0) (b := 4) (c := -0.06) (l := -0.10)
      (m := 0.698) (h.cont.mono (Icc_subset_Icc le_rfl (by norm_num)))
      (fun x hx => h.hasDeriv x (hsub hx)) (by norm_num) ((hSafe _).mp h0).1 ?_ 4
      ⟨by norm_num, le_rfl⟩ (by norm_num)
    intro t ht hvt
    obtain ⟨c, hc1, hc2, hb⟩ := h.balance t (hsub ht)
    have hs := hsafe t ⟨(hsub ht).1, (hsub ht).2.le⟩
    have hb' := hb hs
    rw [uStepL, ite_eq_left ht.2.le, Inet_nominal_high (by linarith)] at hb'
    have hc2' : c ≤ 20 := by simpa [illustrative] using hc2
    have hc1' : (5 : ℝ) ≤ c := by simpa [illustrative] using hc1
    have heps : illustrative.eps = 2 := by norm_num [illustrative]
    rw [heps] at hb'
    have hI : (15.96 : ℝ) ≤ 100 * ((v t) ^ 2 - 2.6 * v t) := by nlinarith
    have hlow : (13.96 : ℝ) ≤ c * rderiv v t := by linarith [(abs_le.mp hb').1]
    have hpos : 0 < rderiv v t := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ c) (not_lt.mp hneg)
      linarith
    have : c * rderiv v t ≤ 20 * rderiv v t := mul_le_mul_of_nonneg_right hc2' hpos.le
    linarith
  exact no_trajectory_through_left_continuous_jump h h0 (t0 := 4) (by norm_num) (by norm_num)
    (by rw [uStepL, ite_eq_left le_rfl])
    (fun t ht => by rw [uStepL, ite_eq_right (not_le.mpr ht.1)]) hv1 hv2

/-- The guarantee for this input is vacuous: from its hypotheses one can
"prove" that the output is 12345 V at every time. -/
theorem stepL_guarantee_proves_anything (v : ℝ → ℝ)
    (h : IsTrajectory illustrative nominal uStepL v 0 10) (h0 : v 0 ∈ illustrative.Safe) :
    ∀ t, v t = 12345 :=
  (stepL_no_trajectory v h h0).elim

/-! ## A single-instant change of the input empties the trajectory set -/

/-- The constant-low input, changed at the single instant `t = 0`. -/
noncomputable def uSpike (t : ℝ) : ℝ := if t = 0 then 1.8 else 0

theorem uSpike_eq_const_off_zero {t : ℝ} (ht : t ≠ 0) : uSpike t = (fun _ : ℝ => (0 : ℝ)) t := by
  simp [uSpike, ht]

/-- With the constant-low input there is a trajectory from every valid-low
initial output (library theorem `illustrative_exists`). -/
theorem const_low_has_trajectory (v₀ : ℝ) (h1 : -0.06 ≤ v₀) (h2 : v₀ ≤ 0.25) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧ IsTrajectory illustrative nominal (fun _ => 0) v 0 10 :=
  illustrative_exists nominal nominal_inBox 10 (by norm_num) (fun _ => 0) (fun _ => 0)
    continuous_const continuous_const 0 10 (by norm_num) (fun t _ => by norm_num) v₀
    ⟨by linarith, by linarith⟩

/-- With `uSpike`, which differs from the constant-low input only at `t = 0`,
there is none. -/
theorem spike_no_trajectory (v : ℝ → ℝ) (h : IsTrajectory illustrative nominal uSpike v 0 10)
    (h1 : -0.06 ≤ v 0) (h2 : v 0 ≤ 0.25) : False := by
  have h0 : v 0 ∈ illustrative.Safe := by
    simp only [Design.Safe, illustrative, mem_Icc]
    constructor <;> linarith
  exact no_trajectory_through_left_continuous_jump h h0 (t0 := 0) le_rfl (by norm_num)
    (by simp [uSpike])
    (fun t ht => by
      have : t ≠ 0 := ne_of_gt ht.1
      simp [uSpike, this]) h1 h2

end Review.P01

#print axioms Review.P01.rderiv_ge_of_right_nhd
#print axioms Review.P01.stepL_no_trajectory
#print axioms Review.P01.stepL_guarantee_proves_anything
#print axioms Review.P01.spike_no_trajectory
#print axioms Review.P01.const_low_has_trajectory
