import VoltageToBit.Examples.Illustrative
import VoltageToBit.Proofs.Contamination

/-!
# Negative controls

Each control changes one thing about the illustrative instance, or about the
claim made for it, and shows that the guarantee is then either *rejected* (a
numeric condition fails) or *refuted* (an explicit trajectory violates the
conclusion). Failing a sufficient condition does not by itself show that a
circuit fails, so the controls exhibit trajectories wherever possible.

1. `badBox_*`: inconsistent parameter bounds. The record is rejected, and the
   box is shown to be empty (the guarantee would have been vacuous).
2. `illustrative_no_early_high`, `early_sampling_counterexample`: insufficient
   observation time. For inputs in `[0, 0.40]` V, a trajectory that starts in
   the safe domain and whose output is valid-low at some instant is not
   valid-high at any time up to 38 ps later; a claimed rise deadline that short
   is false, and a run from 0.25 V that is not valid-high at 38 ps is
   exhibited.
   The lower bound `0 ≤ u` is part of the statement and cannot be dropped. The
   guarantee's own valid-low class is `u ≤ 0.40` V with no lower bound, and for
   that class the sentence fails: with the input held at -1 V there is a run
   that starts at the valid-low level 0.25 V and is valid-high after 38 ps
   (`valid_low_input_can_give_valid_high_within_38ps`).
   This control is far from the proved deadline: 38 ps against a rise deadline
   of 3.43 ns in closed form and 2.26 ns with a certificate
   (`Examples/RefinedDeadlines.lean`). The controls nearest to the proved
   deadlines, in both directions, are in `Examples/Limits.lean`: every rise
   deadline below 2.168 ns and every fall deadline below 1.0234 ns is false.
   `Examples/DeadlineBrackets.lean` states these limits together with the
   proved 2.26 ns and 1.425 ns; for a deadline in between the library has no
   statement in either direction.
3. `miswired_counterexample`, `miswired_never_high`: the two transistors
   exchanged, at nominal parameters. For every horizon `T` there is a run on
   `[0, T]` with a valid-low input whose output starts in `[-0.10, 2.08]` V
   and is never valid-high (informative for `T > 0`; the proof uses the input
   held at 0 V and the output resting at 0.3 V, which the statement does not
   name); and every trajectory of the exchanged network with a valid-low input
   that starts below 1.35 V stays below 1.35 V.
4. `noisy_*`: a disturbance allowance of 10.76 µA, just above the pull-up
   margin of 10.476 µA. The record is rejected, and for every horizon `T` there
   is a trajectory of `noisy` on `[0, T]` that starts in its safe domain, has a
   valid-low input and is never valid-high (informative for `T > 0`; the proof
   uses the input held at 0.40 V and the output resting at 1.34 V, which the
   statement does not name).
5. `illustrative_riseCert_rejected`: a certificate claiming a deadline its
   levels do not support is rejected. This shows that one list of levels fails
   a sufficient condition. That no list of levels is a valid certificate for a
   deadline below 2.168 ns (`riseCert_deadline_ge`), and that every rise
   deadline below 2.168 ns is false (`rise_deadline_counterexample`), is shown
   in `Examples/Limits.lean`.

The statements of this file that assert the existence of a trajectory place
its initial output in the safe domain (`v 0 = 0.25`, `v 0 = 1.35`,
`v 0 ∈ noisy.Safe`). This matters: `IsTrajectory` asks for the current balance
only while the node is in the safe domain, so a statement of the form "there
is a trajectory with ..." that does not place the start there can be met by a
function that stays outside the safe domain, and then exhibits no run of the
circuit.

Two numbers are recorded along the way. `illustrative_max_rise_slew` and
`illustrative_max_fall_slew` are upper bounds on the rising output slew for
inputs restricted to `[0, 0.40]` V and on the falling output slew for inputs
restricted to `[1.25, 1.98]` V. For the guarantee's own input classes,
`u ≤ 0.40` V and `1.25 V ≤ u`, which have no such range, the rising slew over
the first and the falling slew over the second are not bounded
(`valid_low_rise_slew_unbounded`, `valid_high_fall_slew_unbounded`).

Provenance. `valid_low_input_can_give_valid_high_within_38ps` and
`miswired_never_high`, with their lemmas, were contributed by workstream E's
review probes (`review/P03_DeadlineBrackets.lean` in the form ported in
`review/D05_Part1Ports.lean`, and `review/P08_MiswiredUniversal.lean`; findings
E1-04 and E1-05 of `docs/adversarial-review.md`) and ported into this file. The
wording of the two slew bounds follows finding E2-03; the two unboundedness
statements were added with it. The 38 ps statement is stronger here than in
the probe: the probe has `v 0 ≤ 0.25` and an unnamed input, the library
statement names the input, the start and the node equation.
-/

namespace VoltageToBit.Examples

open Set

/-! ## 1. Inconsistent parameter bounds -/

/-- The illustrative record with the NMOS transconductance range inverted
(lower bound 300 above upper bound 240). -/
noncomputable def badBox : Design := { illustrative with knlo := 300 }

theorem badBox_not_admissible : ¬ badBox.Admissible := fun h => by
  have h1 := h.kn_le
  norm_num [badBox, illustrative] at h1

/-- The inverted box contains no parameter choice at all, so any statement
quantified over it would be vacuously true. `Admissible` rules this out. -/
theorem badBox_empty : ∀ θ : Params, ¬ badBox.InBox θ := fun θ h => by
  have h1 := h.kn_ge
  have h2 := h.kn_le
  norm_num [badBox, illustrative] at h1 h2
  linarith

/-! ## 2. Insufficient observation time -/

/-- With the input in `[0, 0.40]` V and the output starting valid-low, the
output is still below `VOH = 1.35` V at every time up to 38 ps later. The
hypothesis `0 ≤ u` is needed: for a valid-low input without a lower bound the
conclusion fails (`valid_low_input_can_give_valid_high_within_38ps`). -/
theorem illustrative_no_early_high (u v : ℝ → ℝ)
    (a b : ℝ) (h : IsTrajectory illustrative u v a b) (h0 : v a ∈ illustrative.Safe)
    (s e : ℝ) (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, 0 ≤ u t ∧ u t ≤ 0.40)
    (hvs : v s ≤ 0.25) :
    ∀ t ∈ Icc s e, t ≤ s + 0.038 → v t < 1.35 := by
  intro t ht htime
  have hbound := h.rise_at_most illustrative_admissible h0 hs he hu hvs t ht
  have hslope : (illustrative.IchargeMax 0 0.40 + illustrative.eps) / illustrative.Clo
      = 28.5508 := by
    norm_num [Design.IchargeMax, illustrative, psq_eq_ite]
  rw [hslope] at hbound
  have : t - s ≤ 0.038 := by linarith
  nlinarith [ht.1]

/-- An upper bound on the rising slew of the illustrative output for inputs
restricted to `[0, 0.40]` V: 28.5508 V/ns. It is the slope that
`IsTrajectory.rise_at_most` gives, for trajectories that start in the safe
domain, with `ulo = 0` and `uhi = 0.40`. It is a bound; no trajectory is shown
to reach it.

The restriction to `[0, 0.40]` V is essential. The guarantee's own valid-low
class is `u ≤ 0.40` V with no lower limit, and for that class the rising slew
is not bounded: see `valid_low_rise_slew_unbounded`. -/
theorem illustrative_max_rise_slew :
    (illustrative.IchargeMax 0 0.40 + illustrative.eps) / illustrative.Clo = 28.5508 := by
  norm_num [Design.IchargeMax, illustrative, psq_eq_ite]

/-- An upper bound on the falling slew of the illustrative output for inputs
restricted to `[1.25, 1.98]` V: 58.3144 V/ns. It is the slope that
`IsTrajectory.fall_at_most` gives, for trajectories that start in the safe
domain, with `ulo = 1.25` and `uhi = 1.98`. It is a bound; no trajectory is
shown to reach it.

The restriction to `[1.25, 1.98]` V is essential. The guarantee's own
valid-high class is `1.25 V ≤ u` with no upper limit, and for that class the
falling slew is not bounded: see `valid_high_fall_slew_unbounded`. -/
theorem illustrative_max_fall_slew :
    (illustrative.IdischargeMax 1.25 1.98 + illustrative.eps) / illustrative.Clo
      = 58.3144 := by
  norm_num [Design.IdischargeMax, illustrative, psq_eq_ite]

/-- A claimed rise deadline of 38 ps is false: there is a trajectory with a
valid-low input at all times that starts at 0.25 V, the highest valid-low
output level, and is not valid-high at `t = 0.038` ns. In the proof the input
is held at 0.2 V, with nominal parameters, capacitance 5 fF and zero
disturbance.

The start is fixed by the statement (`v 0 = 0.25`), so the witness is subject
to the current balance from the first instant. With `v 0 ≤ 0.25` alone the
statement would also be met by a function that stays below the safe domain,
where `IsTrajectory` asks for no balance. -/
theorem early_sampling_counterexample :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧ v 0 = 0.25 ∧
      IsTrajectory illustrative u v 0 10 ∧ v 0.038 < 1.35 := by
  obtain ⟨v, hv0, htraj⟩ := illustrative_exists_const nominal nominal_inBox 5 (by norm_num)
    (fun _ => 0.2) (fun _ => 0) continuous_const continuous_const 0 10 (by norm_num)
    (fun t _ => by norm_num) 0.25 (by norm_num)
  refine ⟨fun _ => 0.2, v, fun t => by norm_num, hv0, htraj, ?_⟩
  have h0 : v 0 ∈ illustrative.Safe := by
    rw [hv0]; norm_num [Design.Safe, illustrative]
  exact illustrative_no_early_high _ v 0 10 htraj h0 0 10 le_rfl le_rfl
    (fun t _ => by norm_num) hv0.le 0.038 (by norm_num) (by norm_num)

/-! ### The input range cannot be dropped

`illustrative_no_early_high` and the two slew bounds assume an input range.
The valid-input classes of the guarantee do not have one: the valid-low class
`u ≤ 0.40` V has no lower bound and the valid-high class `1.25 V ≤ u` has no
upper bound. For these classes the three statements fail, as shown below.
These are facts about the input class of the theorems, not about a device: the
class contains input values far outside any range in which a device model has
a meaning (finding E1-03 of `docs/adversarial-review.md`). -/

/-- A fast pull-up corner of the box: highest supply, strongest PMOS with the
smallest threshold. (For the input -1 V used below the NMOS is off on the whole
safe domain, so `kn` and `Vtn` play no role.) -/
def fastUp : Params := ⟨1.98, 240, 120, 0.45, 0.45⟩

theorem fastUp_inBox : illustrative.InBox fastUp := by
  constructor <;> norm_num [illustrative, fastUp]

/-- At the corner `fastUp` with the input at -1 V, the net current into a node
in `[-0.10, 1.35]` V is at least 167.454 µA. -/
theorem Inet_fastUp_ge {x : ℝ} (h1 : -0.10 ≤ x) (h2 : x ≤ 1.35) :
    (167.454 : ℝ) ≤ Inet fastUp (-1) x := by
  have e1 : psq ((1.98 : ℝ) - -1 - 0.45) = (1.98 - -1 - 0.45) ^ 2 := psq_of_nonneg (by norm_num)
  have e2 : psq (x - -1 - 0.45) = (x - -1 - 0.45) ^ 2 := psq_of_nonneg (by linarith)
  have e3 : psq ((-1 : ℝ) - 0.45) = 0 := psq_of_nonpos (by norm_num)
  have e4 : psq ((-1 : ℝ) - x - 0.45) = 0 := psq_of_nonpos (by linarith)
  simp only [Inet, Ip, In, fastUp, e1, e2, e3, e4]
  nlinarith

/-- **Without the lower bound on the input, 38 ps is enough.** With the input
held at -1 V there is a run of the illustrative record that starts at 0.25 V,
the highest valid-low output level, and is valid-high at `t = 0.038` ns.

The statement names everything about the run:

* the input is the constant -1 V, which is valid-low for the guarantee
  (`u ≤ VIL = 0.40` V, with no lower bound);
* the output starts at 0.25 V;
* it solves the node equation `5 * v' = Inet fastUp (-1) v + 0` on `[0, 10]`:
  the constant box point `fastUp`, a capacitance of 5 fF and zero disturbance;
* it is a trajectory of the illustrative record;
* it is at or above 1.35 V at 38 ps.

Compare `early_sampling_counterexample`: the same start, an input that is also
valid-low (0.2 V in its proof), and the opposite conclusion at the same
instant. So the sentence "no trajectory starting valid-low can be valid-high
within 38 ps" is true for inputs in `[0, 0.40]` V
(`illustrative_no_early_high`) and false for the valid-low class of the
guarantee. -/
theorem valid_low_input_can_give_valid_high_within_38ps :
    ∃ v : ℝ → ℝ, v 0 = 0.25 ∧
      (∀ t ∈ Icc (0 : ℝ) 10,
        HasDerivWithinAt v ((Inet fastUp (-1) (v t) + 0) / 5) (Icc 0 10) t) ∧
      IsTrajectory illustrative (fun _ => -1) v 0 10 ∧ 1.35 ≤ v 0.038 := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (5 : ℝ) := by norm_num [illustrative]
  have hC2 : (5 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (0 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  have hv₀ : (0.25 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm fastUp_inBox (Cf := fun _ => 5) (Kc := 0)
    (fun _ => hC1) (fun x _ y _ => by simp) (u := fun _ => -1)
    (w := fun _ => 0) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet fastUp (-1) (v t) + 0) / 5) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => -1) v 0 10 :=
    IsTrajectory.of_ode fastUp_inBox (Cf := fun _ => 5) (w := fun _ => 0) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨v, hv0, hode, htraj, ?_⟩
  refine rise_by (v := v) (v' := fun t => (Inet fastUp (-1) (v t) + 0) / 5) (a := 0) (b := 10)
    (c := 1.35) (l := 0.25) (m := 33) hcont hder (by norm_num) hv0.ge ?_ 0.038
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  intro t ht hvt
  have hs := hsafe t (Ico_subset_Icc_self ht)
  have hlo : -0.10 ≤ v t := by
    have : -0.10 ≤ v t ∧ v t ≤ 2.08 := by simpa [Design.Safe, illustrative] using hs
    exact this.1
  have := Inet_fastUp_ge hlo hvt
  show (33 : ℝ) ≤ (Inet fastUp (-1) (v t) + 0) / 5
  linarith

/-- **No bound on the rising slew over the valid-low class of the guarantee.**
For every `M` there is a trajectory of the illustrative record with a valid-low
input at all times, started at the valid-low output level 0.25 V, whose right
derivative at time 0 exceeds `M` V/ns. In the proof the input is held at
`-(|M| + 1)` V, with nominal parameters, capacitance 5 fF and zero
disturbance. -/
theorem valid_low_rise_slew_unbounded (M : ℝ) :
    ∃ (u v : ℝ → ℝ) (d : ℝ), (∀ t, u t ≤ 0.40) ∧ v 0 = 0.25 ∧
      IsTrajectory illustrative u v 0 10 ∧ HasDerivWithinAt v d (Ici 0) 0 ∧ M < d := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (5 : ℝ) := by norm_num [illustrative]
  have hC2 : (5 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (0 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  have hv₀ : (0.25 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  have hM0 := abs_nonneg M
  have hM1 := le_abs_self M
  obtain ⟨v, hv0, -, hode⟩ := exists_solution hadm nominal_inBox (Cf := fun _ => 5) (Kc := 0)
    (fun _ => hC1) (fun x _ y _ => by simp) (u := fun _ => -(|M| + 1))
    (w := fun _ => 0) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet nominal (-(|M| + 1)) (v t) + 0) / 5) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => -(|M| + 1)) v 0 10 :=
    IsTrajectory.of_ode nominal_inBox (Cf := fun _ => 5) (w := fun _ => 0) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨fun _ => -(|M| + 1), v, _, fun _ => ?_, hv0, htraj,
    hder 0 ⟨le_rfl, by norm_num⟩, ?_⟩
  · show -(|M| + 1) ≤ (0.40 : ℝ)
    linarith
  · rw [hv0]
    have e1 : psq ((1.8 : ℝ) - -(|M| + 1) - 0.5) = (1.8 - -(|M| + 1) - 0.5) ^ 2 :=
      psq_of_nonneg (by linarith)
    have e2 : psq ((0.25 : ℝ) - -(|M| + 1) - 0.5) = (0.25 - -(|M| + 1) - 0.5) ^ 2 :=
      psq_of_nonneg (by linarith)
    have e3 : psq (-(|M| + 1) - 0.5) = 0 := psq_of_nonpos (by linarith)
    have e4 : psq (-(|M| + 1) - 0.25 - 0.5) = 0 := psq_of_nonpos (by linarith)
    simp only [Inet, Ip, In, nominal, e1, e2, e3, e4]
    nlinarith

/-- **No bound on the falling slew over the valid-high class of the
guarantee.** For every `M` there is a trajectory of the illustrative record
with a valid-high input at all times, started at the valid-high output level
1.35 V, whose right derivative at time 0 is below `-M` V/ns. In the proof the
input is held at `|M| + 2` V, with nominal parameters, capacitance 5 fF and
zero disturbance. -/
theorem valid_high_fall_slew_unbounded (M : ℝ) :
    ∃ (u v : ℝ → ℝ) (d : ℝ), (∀ t, 1.25 ≤ u t) ∧ v 0 = 1.35 ∧
      IsTrajectory illustrative u v 0 10 ∧ HasDerivWithinAt v d (Ici 0) 0 ∧ d < -M := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (5 : ℝ) := by norm_num [illustrative]
  have hC2 : (5 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (0 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  have hv₀ : (1.35 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  have hM0 := abs_nonneg M
  have hM1 := le_abs_self M
  obtain ⟨v, hv0, -, hode⟩ := exists_solution hadm nominal_inBox (Cf := fun _ => 5) (Kc := 0)
    (fun _ => hC1) (fun x _ y _ => by simp) (u := fun _ => |M| + 2)
    (w := fun _ => 0) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet nominal (|M| + 2) (v t) + 0) / 5) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => |M| + 2) v 0 10 :=
    IsTrajectory.of_ode nominal_inBox (Cf := fun _ => 5) (w := fun _ => 0) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨fun _ => |M| + 2, v, _, fun _ => ?_, hv0, htraj,
    hder 0 ⟨le_rfl, by norm_num⟩, ?_⟩
  · show (1.25 : ℝ) ≤ |M| + 2
    linarith
  · rw [hv0]
    have e1 : psq ((1.8 : ℝ) - (|M| + 2) - 0.5) = 0 := psq_of_nonpos (by linarith)
    have e2 : psq ((1.35 : ℝ) - (|M| + 2) - 0.5) = 0 := psq_of_nonpos (by linarith)
    have e3 : psq (|M| + 2 - 0.5) = (|M| + 2 - 0.5) ^ 2 := psq_of_nonneg (by linarith)
    have e4 : psq (|M| + 2 - 1.35 - 0.5) = (|M| + 2 - 1.35 - 0.5) ^ 2 :=
      psq_of_nonneg (by linarith)
    simp only [Inet, Ip, In, nominal, e1, e2, e3, e4]
    nlinarith

/-! ## 3. Miswired transistors -/

/-- Net current into the output node when the transistors are exchanged:
the NMOS pulls up (drain at the supply, source at the output) and the PMOS
pulls down (source at the output, drain at ground), both gates on the input. -/
noncomputable def InetSwapped (θ : Params) (u v : ℝ) : ℝ :=
  θ.kn / 2 * (psq (u - v - θ.Vtn) - psq (u - θ.VDD - θ.Vtn))
    - θ.kp / 2 * (psq (v - u - θ.Vtp) - psq (0 - u - θ.Vtp))

/-- The miswired network is not an inverter: for every horizon `T` there is a
run on `[0, T]` with a valid-low input whose output is never valid-high. The
proof uses the input held at 0 V and the output resting at 0.3 V, the same pair
for every `T`, with zero disturbance and the capacitance and error bounds of the
illustrative instance; the statement itself names neither the input nor the
level, and lets the pair depend on `T`. For `T ≤ 0` the dynamic part is empty
and the statement holds trivially, so it is informative for `T > 0`. -/
theorem miswired_counterexample (T : ℝ) :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧ v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧
      ContinuousOn v (Icc 0 T) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
        (5 : ℝ) ≤ c ∧ c ≤ 20 ∧ |c * v' - InetSwapped nominal (u t) (v t)| ≤ 2) ∧
      ∀ t, v t < 1.35 := by
  refine ⟨fun _ => 0, fun _ => 0.3, fun t => by norm_num, by norm_num, continuousOn_const,
    fun t _ => ⟨0, 5, hasDerivWithinAt_const t _ _, le_rfl, by norm_num, ?_⟩,
    fun t => by norm_num⟩
  norm_num [InetSwapped, nominal, psq_eq_ite]

/-- With a valid-low input, at any level `L ≥ 1.2` V the miswired network (at
nominal parameters) pulls the node *down* with at least `50 * (L - 0.9) ^ 2` µA,
which is at least 4.5 µA. -/
theorem InetSwapped_le {u L : ℝ} (hu : u ≤ 0.40) (hL1 : 1.2 ≤ L) :
    InetSwapped nominal u L ≤ -(50 * (L - 0.9) ^ 2) := by
  have e1 : psq (u - L - 0.5) = 0 := psq_of_nonpos (by linarith)
  have e2 : psq (u - 1.8 - 0.5) = 0 := psq_of_nonpos (by linarith)
  have e3 : psq (L - 0.40 - 0.5) - psq ((0 : ℝ) - 0.40 - 0.5)
      ≤ psq (L - u - 0.5) - psq (0 - u - 0.5) :=
    psq_sub_le_psq_sub (by linarith) (by linarith) (by linarith)
  rw [psq_of_nonneg (by linarith : (0 : ℝ) ≤ L - 0.40 - 0.5),
    psq_of_nonpos (by norm_num : (0 : ℝ) - 0.40 - 0.5 ≤ 0)] at e3
  simp only [InetSwapped, nominal, e1, e2]
  nlinarith

/-- **The miswired network never produces a valid-high output from a valid-low
input.** Take the exchanged-transistor network of `miswired_counterexample`
(nominal parameters, a capacitance in `[5, 20]` fF and a current error of at
most 2 µA at each instant). For every input that is valid-low on `[a, b)` and
every trajectory whose output starts below `VOH = 1.35` V, the output stays
below 1.35 V on all of `[a, b]`. So the constant 0.3 V of
`miswired_counterexample` is not a cherry-picked equilibrium: no run of the
miswired network that starts below `VOH` with a valid-low input ever becomes
valid-high.

Scope. This is a statement about the function `InetSwapped` at nominal
parameters, the library's model of the exchanged network. The library has no
netlist layer: the topology is fixed inside `Inet`, so no control can show
that a checker would notice a miswired design. -/
theorem miswired_never_high {u v : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn v (Icc a b))
    (hincl : ∀ t ∈ Ico a b, ∃ v' c : ℝ, HasDerivWithinAt v v' (Ici t) t ∧
      (5 : ℝ) ≤ c ∧ c ≤ 20 ∧ |c * v' - InetSwapped nominal (u t) (v t)| ≤ 2)
    (hu : ∀ t ∈ Ico a b, u t ≤ 0.40) (h0 : v a < 1.35) :
    ∀ t ∈ Icc a b, v t < 1.35 := by
  -- a barrier level strictly below 1.35 that the initial state does not exceed
  set L : ℝ := max (v a) 1.2 with hL
  have hL1 : 1.2 ≤ L := le_max_right _ _
  have hL2 : L < 1.35 := max_lt h0 (by norm_num)
  have hder : ∀ t ∈ Ico a b, HasDerivWithinAt v (rderiv v t) (Ici t) t := by
    intro t ht
    obtain ⟨v', c, hd, -⟩ := hincl t ht
    exact hd.differentiableWithinAt.hasDerivWithinAt
  have hbar : ∀ t ∈ Icc a b, v t ≤ L := by
    refine barrier_le hcont hder (le_max_left _ _) ?_
    intro s hs hvs
    obtain ⟨v', c, hd, hc1, hc2, hb⟩ := hincl s hs
    have hv' : rderiv v s = v' := hd.derivWithin (uniqueDiffWithinAt_Ici s)
    rw [hvs] at hb
    have hI := InetSwapped_le (hu s hs) hL1
    have hsq : (0.09 : ℝ) ≤ (L - 0.9) ^ 2 := by nlinarith
    have hneg : c * v' < 0 := by linarith [(abs_le.mp hb).2]
    rw [hv']
    by_contra hpos
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ c) (not_lt.mp hpos)
    linarith
  intro t ht
  exact lt_of_le_of_lt (hbar t ht) hL2

/-! ## 4. A disturbance allowance that destroys the pull-up margin -/

/-- The illustrative record with the disturbance allowance raised from 2 µA to
10.76 µA, just above the pull-up margin `Iup VOH = 10.476` µA. -/
noncomputable def noisy : Design := { illustrative with eps := 10.76 }

/-- The weak pull-up corner of the box: lowest supply, weakest PMOS with the
largest threshold, strongest NMOS with the smallest threshold. -/
def weakCorner : Params := ⟨1.62, 240, 80, 0.45, 0.60⟩

theorem weakCorner_inBox : noisy.InBox weakCorner := by
  constructor <;> norm_num [noisy, illustrative, weakCorner]

theorem noisy_not_admissible : ¬ noisy.Admissible := fun h => by
  have h1 := h.up
  norm_num [noisy, illustrative, Design.Iup, psq_eq_ite] at h1

/-- With the larger allowance the guarantee is false, not merely unproved: for
every horizon `T` there is a trajectory of `noisy` on `[0, T]` that starts in
its safe domain, has a valid-low input and is never valid-high. The proof uses
the weak corner, the input held at 0.40 V and the output resting at 1.34 V,
below `VOH = 1.35` V, the same pair for every `T`; the statement itself does not
name them and lets the pair depend on `T`. For `T ≤ 0` it holds trivially, so
it is informative for `T > 0`. -/
theorem noisy_counterexample (T : ℝ) :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ noisy.VIL) ∧ v 0 ∈ noisy.Safe ∧
      IsTrajectory noisy u v 0 T ∧ ∀ t, v t < noisy.VOH := by
  refine ⟨fun _ => 0.40, fun _ => 1.34, fun t => by norm_num [noisy, illustrative],
    by norm_num [Design.Safe, noisy, illustrative],
    ⟨continuousOn_const, fun t _ => ⟨0, 5, hasDerivWithinAt_const t _ _, ?_, ?_,
      fun _ => ⟨weakCorner, weakCorner_inBox, ?_⟩⟩⟩,
    fun t => by norm_num [noisy, illustrative]⟩
  · norm_num [noisy, illustrative]
  · norm_num [noisy, illustrative]
  · norm_num [noisy, illustrative, weakCorner, Inet, Ip, In, psq_eq_ite, abs_le]

/-! ## 5. An unjustified certificate is rejected -/

/-- The three-level certificate supports a 2.34 ns deadline
(`illustrative_riseCert_3`) but not a 2.0 ns one. -/
theorem illustrative_riseCert_rejected : ¬ illustrative.ValidRiseCert 1.0 [1.2, 1.35] 2.0 := by
  rintro ⟨-, -, hτ⟩
  norm_num [riseTime, Design.upSegs, Design.Iup, illustrative, psq_eq_ite] at hτ

end VoltageToBit.Examples
