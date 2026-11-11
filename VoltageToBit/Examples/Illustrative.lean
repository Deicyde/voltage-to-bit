import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import VoltageToBit.Examples.IllustrativeDesign
import VoltageToBit.Proofs.Existence
import VoltageToBit.Proofs.AtSupply
import VoltageToBit.Proofs.Certificate
import VoltageToBit.Proofs.ModelError

/-!
# A concrete instance: the illustrative 1.8 V-class inverter

All numbers come from `designs/illustrative-1v8.json` (units V, µA, fF, ns).
They are **illustrative**: plausible orders of magnitude, not fitted to any
process, device model or measurement.

* `illustrative_admissible`: the record satisfies every numeric condition.
* `illustrative_guarantee`: the universal guarantee with explicit numbers.
* `illustrative_exists`: trajectories exist from every initial state in the
  safe domain, for every continuous input and every interval.
* `illustrative_scenario`: one fully explicit run (nominal parameters, a
  concrete input waveform, a concrete nonzero disturbance, an initial state in
  the undefined band) in which both logic directions occur and each is followed
  by an observation window of positive length.
* `illustrative_feedthrough_scenario`: one explicit run in which the output
  node has a gate-drain capacitance and one aggressor, the input keeps moving,
  and the displacement currents fit the allowance. It is the witness that the
  hypotheses of `IsTrajectory.of_charge_balance` can be met.
-/

namespace VoltageToBit.Examples

open Set

/-- The illustrative record satisfies every numeric admissibility condition.
Each field is checked by arithmetic on the numbers of the record. -/
theorem illustrative_admissible : illustrative.Admissible := by
  constructor <;>
    norm_num [illustrative, Design.Iup, Design.Idn, Design.RhiP, Design.RhiN, Design.RloN,
      Design.RloP, psq_eq_ite]

/-- The disturbance allowance of the instance is strictly positive. -/
theorem illustrative_eps_pos : 0 < illustrative.eps := by norm_num [illustrative]

/-! ## The closed-form margins and deadlines, evaluated exactly -/

theorem illustrative_Iup : illustrative.Iup illustrative.VOH = 10.476 := by
  norm_num [illustrative, Design.Iup, psq_eq_ite]

theorem illustrative_Idn : illustrative.Idn illustrative.VOL = 16.296 := by
  norm_num [illustrative, Design.Idn, psq_eq_ite]

theorem illustrative_RhiP : illustrative.RhiP = 2.4 := by
  norm_num [illustrative, Design.RhiP, psq_eq_ite]

theorem illustrative_RhiN : illustrative.RhiN = 2.312 := by
  norm_num [illustrative, Design.RhiN, psq_eq_ite]

theorem illustrative_RloN : illustrative.RloN = 3.04 := by
  norm_num [illustrative, Design.RloN, psq_eq_ite]

theorem illustrative_RloP : illustrative.RloP = 3.136 := by
  norm_num [illustrative, Design.RloP, psq_eq_ite]

theorem illustrative_tauUp : illustrative.tauUp = 7250 / 2119 := by
  norm_num [illustrative, Design.tauUp, Design.Iup, psq_eq_ite]

theorem illustrative_tauDn : illustrative.tauDn = 4575 / 1787 := by
  norm_num [illustrative, Design.tauDn, Design.Idn, psq_eq_ite]

theorem illustrative_tauUp_le : illustrative.tauUp ≤ 3.43 := by
  rw [illustrative_tauUp]; norm_num

theorem illustrative_tauDn_le : illustrative.tauDn ≤ 2.57 := by
  rw [illustrative_tauDn]; norm_num

/-! ## The guarantee with explicit numbers -/

/-- **Universal guarantee for the illustrative inverter.** For every input
function `u` and every trajectory `v` on `[a, b]` that starts in
`[-0.10, 2.08]` V:

1. `v` stays in `[-0.10, 2.08]` V;
2. whenever `u ≤ 0.40` V on a window `[s, e)` within `[a, b]`, `v ≥ 1.35` V on
   `[s + 3.43 ns, e]`;
3. whenever `u ≥ 1.25` V on a window `[s, e)` within `[a, b]`, `v ≤ 0.25` V on
   `[s + 2.57 ns, e]`.

The closed-form deadlines are `7250/2119 ≈ 3.4214` ns and `4575/1787 ≈ 2.5602`
ns; 3.43 and 2.57 round them up.

The trajectory notion allows, at each instant, any capacitance in `[5, 20]` fF,
any parameter point of the box, and any unmodelled current of magnitude at most
`2` µA. -/
theorem illustrative_guarantee (u v : ℝ → ℝ)
    (a b : ℝ) (h : IsTrajectory illustrative u v a b) (h0 : v a ∈ Icc (-0.10 : ℝ) 2.08) :
    (∀ t ∈ Icc a b, v t ∈ Icc (-0.10 : ℝ) 2.08) ∧
    (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
      ∀ t ∈ Icc s e, s + 3.43 ≤ t → 1.35 ≤ v t) ∧
    (∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
      ∀ t ∈ Icc s e, s + 2.57 ≤ t → v t ≤ 0.25) := by
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  have h0' : v a ∈ illustrative.Safe := by rw [hsafe]; exact h0
  refine ⟨fun t ht => ?_, fun s e hs he hu t ht htime => ?_, fun s e hs he hu t ht htime => ?_⟩
  · rw [← hsafe]
    exact h.safe illustrative_admissible h0' t ht
  · have := h.rise illustrative_admissible h0' hs he
      (fun x hx => by simpa [illustrative] using hu x hx) t ht
      (by linarith [illustrative_tauUp_le])
    simpa [illustrative] using this
  · have := h.fall illustrative_admissible h0' hs he
      (fun x hx => by simpa [illustrative] using hu x hx) t ht
      (by linarith [illustrative_tauDn_le])
    simpa [illustrative] using this

/-- **Trajectories exist** for the illustrative inverter: for every continuous
input, every interval and every initial state in the safe domain there is a
trajectory. The statement takes a constant parameter point of the box, a
voltage-dependent capacitance with values in `[5, 20]` fF that is Lipschitz on
the safe domain, and a continuous disturbance of magnitude at most `2` µA, but
its conclusion does not mention them: they serve to build the trajectory. A
run that solves the node equation with given data is `exists_solution`
followed by `IsTrajectory.of_ode`. -/
theorem illustrative_exists (θ : Params) (hθ : illustrative.InBox θ) (Cf : ℝ → ℝ)
    (hCf : ∀ x, Cf x ∈ Icc (5 : ℝ) 20) (Kc : ℝ)
    (hCfLip : ∀ x ∈ Icc (-0.10 : ℝ) 2.08, ∀ y ∈ Icc (-0.10 : ℝ) 2.08,
      |Cf x - Cf y| ≤ Kc * |x - y|)
    (u w : ℝ → ℝ) (hu : Continuous u) (hw : Continuous w)
    (a b : ℝ) (hab : a ≤ b) (hwb : ∀ t ∈ Icc a b, |w t| ≤ 2) (v₀ : ℝ)
    (hv₀ : v₀ ∈ Icc (-0.10 : ℝ) 2.08) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ IsTrajectory illustrative u v a b := by
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  refine exists_trajectory illustrative_admissible hθ (Cf := Cf) (Kc := Kc) ?_ ?_ hu hw hab ?_ ?_
  · intro x
    simpa [illustrative] using hCf x
  · rw [hsafe]
    exact hCfLip
  · simpa [illustrative] using hwb
  · rw [hsafe]
    exact hv₀

/-- The constant-capacitance special case of `illustrative_exists` (its
conclusion, too, does not mention the data it takes). -/
theorem illustrative_exists_const (θ : Params) (hθ : illustrative.InBox θ) (C : ℝ)
    (hC : C ∈ Icc (5 : ℝ) 20) (u w : ℝ → ℝ) (hu : Continuous u) (hw : Continuous w)
    (a b : ℝ) (hab : a ≤ b) (hwb : ∀ t ∈ Icc a b, |w t| ≤ 2) (v₀ : ℝ)
    (hv₀ : v₀ ∈ Icc (-0.10 : ℝ) 2.08) :
    ∃ v : ℝ → ℝ, v a = v₀ ∧ IsTrajectory illustrative u v a b :=
  illustrative_exists θ hθ (fun _ => C) (fun _ => hC) 0 (fun x _ y _ => by simp) u w hu hw
    a b hab hwb v₀ hv₀

/-! ## One fully explicit run -/

/-- Nominal parameters, a point of the box (`nominal_inBox`). The supply
(1.8 V) and the two transconductances (200 and 100 µA/V²) are the centres of
their ranges. The two thresholds (0.5 V) are not: their ranges are
`[0.45, 0.60]` V, with centre 0.525 V. -/
def nominal : Params := ⟨1.8, 200, 100, 0.5, 0.5⟩

theorem nominal_inBox : illustrative.InBox nominal := by
  constructor <;> norm_num [illustrative, nominal]

/-- A concrete input: high (1.8 V) until `t = 4` ns, then a linear fall to 0 V
in 0.2 ns, then low. -/
noncomputable def uRamp (t : ℝ) : ℝ := max 0 (min 1.8 (1.8 - 9 * (t - 4)))

theorem continuous_uRamp : Continuous uRamp := by
  unfold uRamp
  fun_prop

theorem uRamp_high {t : ℝ} (ht : t ≤ 4) : uRamp t = 1.8 := by
  unfold uRamp
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem uRamp_low {t : ℝ} (ht : 4.16 ≤ t) : uRamp t ≤ 0.40 := by
  unfold uRamp
  refine max_le (by norm_num) ((min_le_right _ _).trans ?_)
  linarith

/-- A concrete nonzero disturbance: a 2 µA sinusoid. -/
noncomputable def wSin (t : ℝ) : ℝ := 2 * Real.sin t

theorem continuous_wSin : Continuous wSin := by
  unfold wSin
  fun_prop

theorem abs_wSin_le (t : ℝ) : |wSin t| ≤ 2 := by
  unfold wSin
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [Real.abs_sin_le_one t]

/-- **An explicit run.** Nominal parameters, capacitance 10 fF, the input
`uRamp`, the disturbance `wSin`, initial output 1.0 V (which decodes to
*undefined*), horizon 10 ns. A solution of the ODE exists; it is a trajectory;
the output is valid-low throughout `[2.57, 4]` ns (input high since `t = 0`) and
valid-high throughout `[7.59, 10]` ns (input low since `t = 4.16`). Both windows
have positive length.

This run is a mathematical witness, not a physically budgeted scenario. The
input falls at 9 V/ns; in a real inverter the gate-drain capacitance `C_M`
would inject `C_M · du/dt` into the output node during that edge, which alone
reaches the whole 2 µA allowance at `C_M = 0.22` fF, and `wSin` already uses
the full allowance. See `docs/model.md`, section 7.4. -/
theorem illustrative_scenario :
    ∃ v : ℝ → ℝ, v 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 10,
        HasDerivWithinAt v ((Inet nominal (uRamp t) (v t) + wSin t) / 10) (Icc 0 10) t) ∧
      IsTrajectory illustrative uRamp v 0 10 ∧
      (∀ t ∈ Icc (0 : ℝ) 10, v t ∈ Icc (-0.10 : ℝ) 2.08) ∧
      (∀ t ∈ Icc (2.57 : ℝ) 4, illustrative.decodeOut (v t) = some false) ∧
      (∀ t ∈ Icc (7.59 : ℝ) 10, illustrative.decodeOut (v t) = some true) := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (10 : ℝ) := by norm_num [illustrative]
  have hC2 : (10 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |wSin t| ≤ illustrative.eps := fun t _ => by
    simpa [illustrative] using abs_wSin_le t
  have hv₀ : (1 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm nominal_inBox (Cf := fun _ => 10)
    (Kc := 0) (fun _ => hC1) (fun x _ y _ => by simp) continuous_uRamp
    continuous_wSin (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have htraj : IsTrajectory illustrative uRamp v 0 10 :=
    IsTrajectory.of_ode nominal_inBox (Cf := fun _ => 10) (w := wSin) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht))
      (fun t ht => (hode t ht).continuousWithinAt)
      (fun t ht => ⟨_, (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht), by field_simp⟩)
  have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
  obtain ⟨hdom, hrise, hfall⟩ := illustrative_guarantee uRamp v 0 10 htraj
    (by simpa [Design.Safe, illustrative] using h0)
  have hoo : illustrative.VOL < illustrative.VOH := by norm_num [illustrative]
  refine ⟨v, hv0, hode, htraj, hdom, fun t ht => ?_, fun t ht => ?_⟩
  · -- input high on [0, 4): output low on [2.57, 4]
    have := hfall 0 4 le_rfl (by norm_num)
      (fun x hx => by rw [uRamp_high hx.2.le]; norm_num) t ⟨by linarith [ht.1], ht.2⟩
      (by linarith [ht.1])
    exact decode_eq_false_iff.mpr (by simpa [illustrative] using this)
  · -- input low on [4.16, 10): output high on [7.59, 10]
    have := hrise 4.16 10 (by norm_num) le_rfl
      (fun x hx => uRamp_low hx.1) t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])
    exact (decode_eq_true_iff hoo).mpr (by simpa [illustrative] using this)

/-- The initial state of the explicit run is in the undefined band: it does not
decode to a bit. -/
theorem illustrative_initial_undefined : illustrative.decodeOut 1 = none := by
  rw [Design.decodeOut, decode_eq_none_iff]
  norm_num [illustrative]

/-! ## An explicit run with feedthrough and coupling inside the allowance

The run above ramps its input at 9 V/ns and says nothing about the gate-drain
capacitance. The run below is the complementary witness: the output node has a
gate-drain capacitance and one aggressor, the input keeps moving, and the
displacement currents fit the allowance by arithmetic on stated coefficients. -/

/-- A valid-low input that keeps moving: it stays in `[0, 0.40]` V and its slew
is at most 2 V/ns. -/
noncomputable def uFeed (t : ℝ) : ℝ := 0.2 + 0.2 * Real.sin (10 * t)

/-- An aggressor waveform: it stays in `[0.4, 1.4]` V and its slew is at most
5 V/ns. -/
noncomputable def gFeed (t : ℝ) : ℝ := 0.9 + 0.5 * Real.sin (10 * t)

theorem continuous_uFeed : Continuous uFeed := by
  unfold uFeed
  fun_prop

theorem uFeed_le (t : ℝ) : uFeed t ≤ 0.40 := by
  unfold uFeed
  linarith [Real.sin_le_one (10 * t)]

theorem hasDerivAt_uFeed (t : ℝ) : HasDerivAt uFeed (2 * Real.cos (10 * t)) t := by
  have h := ((((hasDerivAt_id t).const_mul (10 : ℝ)).sin).const_mul (0.2 : ℝ)).const_add
    (0.2 : ℝ)
  refine h.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_gFeed (t : ℝ) : HasDerivAt gFeed (5 * Real.cos (10 * t)) t := by
  have h := ((((hasDerivAt_id t).const_mul (10 : ℝ)).sin).const_mul (0.5 : ℝ)).const_add
    (0.9 : ℝ)
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- **An explicit run with gate-drain feedthrough and one aggressor.** Nominal
parameters; three linear capacitors at the output node, 9.4 fF to ground,
0.5 fF to the input `uFeed` and 0.1 fF to the aggressor `gFeed` (10 fF in
total); a residual current of `0.5 sin t` µA; initial output 1.0 V; horizon
10 ns. A function `v` exists whose node charge obeys the charge balance (second
conjunct); it is a trajectory, by `IsTrajectory.of_charge_balance`; and the
output is valid-high throughout `[3.43, 10]` ns (input valid-low since `t = 0`).

The budget is `0.5 fF · 2 V/ns + 0.1 fF · 5 V/ns + 0.5 µA = 2 µA`, the whole
allowance. The coefficients are those of the illustrative budget in
`designs/illustrative-1v8.notes.md`, with its remaining shares (0.5 µA in
total) represented by the residual. The input and the aggressor are continuous
with derivatives of magnitude at most 2 V/ns and 5 V/ns, and the node charge
is continuous because `v`, `uFeed` and `gFeed` are. So the hypotheses of
`IsTrajectory.of_charge_balance` can be met with nonzero coupling and a moving
input, and the guarantee then applies.

This is a mathematical witness inside an assumed budget. No coefficient is
taken from a device, an input that slews at no more than 2 V/ns is slow (a
full swing would take about 0.9 ns), and only the rising direction of the
output occurs. -/
theorem illustrative_feedthrough_scenario :
    ∃ v : ℝ → ℝ, v 0 = 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 10, HasDerivWithinAt
        (fun s => 9.4 * v s + 0.5 * (v s - uFeed s) + 0.1 * (v s - gFeed s))
        (Inet nominal (uFeed t) (v t) + 0.5 * Real.sin t) (Ici t) t) ∧
      IsTrajectory illustrative uFeed v 0 10 ∧
      (∀ t ∈ Icc (3.43 : ℝ) 10, illustrative.decodeOut (v t) = some true) := by
  have hadm := illustrative_admissible
  -- feedthrough, coupling and residual together, as one disturbance of the square-law ODE
  have hwc : Continuous (fun t : ℝ => 0.5 * (2 * Real.cos (10 * t))
      + 0.1 * (5 * Real.cos (10 * t)) + 0.5 * Real.sin t) := by fun_prop
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |0.5 * (2 * Real.cos (10 * t))
      + 0.1 * (5 * Real.cos (10 * t)) + 0.5 * Real.sin t| ≤ illustrative.eps := by
    intro t _
    have h1 := Real.neg_one_le_cos (10 * t)
    have h2 := Real.cos_le_one (10 * t)
    have h3 := Real.neg_one_le_sin t
    have h4 := Real.sin_le_one t
    have he : illustrative.eps = 2 := by norm_num [illustrative]
    rw [he, abs_le]
    constructor <;> linarith
  have hv₀ : (1 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, hode⟩ := exists_solution hadm nominal_inBox (Cf := fun _ => 10)
    (Kc := 0) (fun _ => by norm_num [illustrative]) (fun x _ y _ => by simp) continuous_uFeed
    hwc (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  -- charge balance: 9.4 fF to ground, 0.5 fF to the input, 0.1 fF to the aggressor
  have hq : ∀ t ∈ Ico (0 : ℝ) 10, HasDerivWithinAt
      (fun s => 9.4 * v s + 0.5 * (v s - uFeed s) + 0.1 * (v s - gFeed s))
      (Inet nominal (uFeed t) (v t) + 0.5 * Real.sin t) (Ici t) t := by
    intro t ht
    have hv := (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    have hu := (hasDerivAt_uFeed t).hasDerivWithinAt (s := Ici t)
    have hg := (hasDerivAt_gFeed t).hasDerivWithinAt (s := Ici t)
    have h := ((hv.const_mul (9.4 : ℝ)).add ((hv.sub hu).const_mul (0.5 : ℝ))).add
      ((hv.sub hg).const_mul (0.1 : ℝ))
    refine (h.congr (fun s _ => rfl) rfl).congr_deriv ?_
    ring
  -- continuity of the node voltage, of the input and of the aggressor, hence of the charge
  have hvcont : ContinuousOn v (Icc (0 : ℝ) 10) := fun t ht => (hode t ht).continuousWithinAt
  have hucont : ContinuousOn uFeed (Icc (0 : ℝ) 10) := continuous_uFeed.continuousOn
  have hgcont : ContinuousOn gFeed (Icc (0 : ℝ) 10) := by
    unfold gFeed
    fun_prop
  have hqcont : ContinuousOn
      (fun s => 9.4 * v s + 0.5 * (v s - uFeed s) + 0.1 * (v s - gFeed s)) (Icc (0 : ℝ) 10) :=
    ((hvcont.const_mul 9.4).add ((hvcont.sub hucont).const_mul 0.5)).add
      ((hvcont.sub hgcont).const_mul 0.1)
  have htraj : IsTrajectory illustrative uFeed v 0 10 :=
    IsTrajectory.of_charge_balance (θ := nominal) (g := gFeed)
      (du := fun t => 2 * Real.cos (10 * t)) (dg := fun t => 5 * Real.cos (10 * t))
      (w := fun t => 0.5 * Real.sin t) (CL := 9.4) (CM := 0.5) (Cc := 0.1)
      (Su := 2) (Sg := 5) (εw := 0.5)
      (by norm_num) (by norm_num) (by norm_num [illustrative]) (by norm_num [illustrative])
      (by norm_num [illustrative]) (by norm_num [illustrative]) nominal_inBox
      (fun t _ => (hasDerivAt_uFeed t).hasDerivWithinAt)
      (fun t _ => (hasDerivAt_gFeed t).hasDerivWithinAt)
      (fun t _ => by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [Real.abs_cos_le_one (10 * t)])
      (fun t _ => by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
        linarith [Real.abs_cos_le_one (10 * t)])
      (fun t _ => by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 0.5)]
        linarith [Real.abs_sin_le_one t])
      hqcont hucont hgcont hq
  have h0 : v 0 ∈ Icc (-0.10 : ℝ) 2.08 := by
    rw [hv0]; norm_num
  obtain ⟨-, hrise, -⟩ := illustrative_guarantee uFeed v 0 10 htraj h0
  have hoo : illustrative.VOL < illustrative.VOH := by norm_num [illustrative]
  refine ⟨v, hv0, hq, htraj, fun t ht => ?_⟩
  have := hrise 0 10 le_rfl le_rfl (fun x _ => uFeed_le x) t ⟨by linarith [ht.1], ht.2⟩
    (by linarith [ht.1])
  exact (decode_eq_true_iff hoo).mpr (by simpa [illustrative] using this)

/-! ## The safe domain measured from the actual supply -/

/-- For a run at constant parameters, the output of the illustrative inverter
stays within 0.10 V of its own rails: a solution of the node equation that
starts in `[-0.10, θ.VDD + 0.10]` V stays there. (The fixed safe domain of the
record reaches 2.08 V whatever the supply is.) This is a statement about a run
at one supply value; for a supply that moves in time only the fixed domain is
proved (`Proofs/AtSupply.lean`). -/
theorem illustrative_safe_atSupply (θ : Params) (hθ : illustrative.InBox θ)
    (Cf w u v : ℝ → ℝ) (a b : ℝ) (hCf : ∀ x, Cf x ∈ Icc (5 : ℝ) 20)
    (hw : ∀ t ∈ Ico a b, |w t| ≤ 2) (hcont : ContinuousOn v (Icc a b))
    (hode : ∀ t ∈ Ico a b, ∃ v' : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      Cf (v t) * v' = Inet θ (u t) (v t) + w t)
    (h0 : v a ∈ Icc (-0.10 : ℝ) (θ.VDD + 0.10)) :
    ∀ t ∈ Icc a b, v t ∈ Icc (-0.10 : ℝ) (θ.VDD + 0.10) := by
  have key := solution_safe_atSupply (D := illustrative) illustrative_admissible hθ
    (Cf := Cf) (w := w)
    (by intro x; simpa [illustrative] using hCf x) (by simpa [illustrative] using hw)
    hcont hode
  have e : θ.VDD + (illustrative.Vhi - illustrative.VDDhi) = θ.VDD + 0.10 := by
    norm_num [illustrative]
  have e2 : illustrative.Vlo = -0.10 := by norm_num [illustrative]
  rw [e, e2] at key
  exact key h0

/-! ## A refined, still fully proved, rise deadline -/

/-- A three-level certificate improves the rise deadline from 3.43 ns to
2.34 ns under exactly the same assumptions. -/
theorem illustrative_riseCert_3 : illustrative.ValidRiseCert 1.0 [1.2, 1.35] 2.34 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [RiseSegs, finalLevel, riseTime, Design.upSegs, Design.Iup, illustrative,
      psq_eq_ite]

end VoltageToBit.Examples
