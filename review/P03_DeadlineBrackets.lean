import VoltageToBit

/-!
# Probe P03 (workstream E): how early is too early? Sharper negative controls

The library's "insufficient observation time" control refutes a 38 ps rise
deadline (`early_sampling_counterexample`) and merely *rejects* a 2.0 ns
certificate (`illustrative_riseCert_rejected`). Between 0.038 ns and the proved
3.43 ns (2.34 ns with the certificate) nothing is shown. This probe closes most
of that gap with actual trajectories of the illustrative instance, and tests
one sentence of the negative-control header.

* `rise_deadline_2p16_is_false`: a trajectory in the box, valid-low input,
  initial state in the safe domain, admissible disturbance, that is **not**
  valid-high at 2.16 ns. The same trajectory is valid-high from 2.34 ns on.
  So the best rise deadline of the instance lies in `(2.16, 2.34]` ns
  (numerically 2.2512 ns, `review/num/n03_worst_case_delay.py`).
* `no_riseCert_at_2p16`: consequently NO list of levels is a valid rising
  certificate for 2.16 ns; the certificate mechanism cannot be gamed below the
  model's own worst case.
* `rise_deadline_1p64_is_false_from_valid_low`: the same with a valid-low
  initial output.
* `fall_deadline_1p0_is_false`, `illustrative_fallCert_3`: the falling
  direction, for which the library has neither a contamination bound nor an
  instantiated certificate: 1.0 ns is false, 1.51 ns is proved.
* `valid_low_input_can_give_valid_high_within_38ps`: the header of
  `Examples/NegativeControls.lean` says "No trajectory starting valid-low can
  be valid-high within 38 ps". That sentence is false for the trajectory class
  of the guarantee, whose valid-low inputs are all `u ≤ VIL` with no lower
  bound: with `u = -1 V` at the fast corner the output is valid-high at 38 ps.
  (The theorem `illustrative_no_early_high` itself is fine; it assumes
  `0 ≤ u`.)
-/

open Set
open VoltageToBit VoltageToBit.Examples

namespace Review.P03

/-! ## Slowest rise: weak pull-up corner, largest capacitance, adverse disturbance -/

/-- Lowest supply, weakest PMOS with the largest threshold. (The NMOS choice is
irrelevant here: with `Vtn = 0.60` it is off on the whole safe domain.) -/
def slowUp : Params := ⟨1.62, 240, 80, 0.60, 0.60⟩

theorem slowUp_inBox : illustrative.InBox slowUp := by
  constructor <;> norm_num [illustrative, slowUp]

theorem Inet_slowUp_le {x : ℝ} (h1 : -0.10 ≤ x) : Inet slowUp 0.40 x ≤ 15.376 := by
  have e1 : psq ((1.62 : ℝ) - 0.40 - 0.60) = (1.62 - 0.40 - 0.60) ^ 2 :=
    psq_of_nonneg (by norm_num)
  have e3 : psq ((0.40 : ℝ) - 0.60) = 0 := psq_of_nonpos (by norm_num)
  have e4 : psq ((0.40 : ℝ) - x - 0.60) = 0 := psq_of_nonpos (by linarith)
  have e2 := psq_nonneg (x - 0.40 - 0.60)
  simp only [Inet, Ip, In, slowUp, e1, e3, e4]
  nlinarith

/-- The slowest admissible run from the initial state `v₀`: it exists, it is a
trajectory, and it stays below the line `v₀ + 0.6688 t`. -/
theorem slow_rise_run (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧ IsTrajectory illustrative slowUp (fun _ => 0.40) v 0 10 ∧
      ∀ t ∈ Icc (0 : ℝ) 10, v t ≤ v₀ + 0.6688 * t := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (20 : ℝ) := by norm_num [illustrative]
  have hC2 : (20 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (-2 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm slowUp_inBox hC1 (u := fun _ => 0.40)
    (w := fun _ => -2) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet slowUp 0.40 (v t) + -2) / 20) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative slowUp (fun _ => 0.40) v 0 10 :=
    IsTrajectory.of_ode (Cf := fun _ => 20) (w := fun _ => -2) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨v, hv0, htraj, fun t ht => ?_⟩
  refine image_le_of_deriv_right_le_deriv_boundary
    (f := v) (f' := fun t => (Inet slowUp 0.40 (v t) + -2) / 20) (a := 0) (b := 10) hcont hder
    (B := fun t => v₀ + 0.6688 * t) (B' := fun _ => 0.6688) (by simp [hv0]) (by fun_prop)
    (fun x _ => by
      have h := ((hasDerivAt_id x).const_mul (0.6688 : ℝ)).const_add v₀
      simpa using h.hasDerivWithinAt)
    (fun x hx => ?_) ht
  have hs := hsafe x (Ico_subset_Icc_self hx)
  have hlo : -0.10 ≤ v x := by
    have : -0.10 ≤ v x ∧ v x ≤ 2.08 := by simpa [Design.Safe, illustrative] using hs
    exact this.1
  have := Inet_slowUp_le hlo
  show (Inet slowUp 0.40 (v x) + -2) / 20 ≤ 0.6688
  linarith

/-- **A 2.16 ns rise deadline is false** for the illustrative instance; and on
the very same run the output is valid-high from 2.34 ns on (certificate). -/
theorem rise_deadline_2p16_is_false :
    ∃ (θ : Params) (u v : ℝ → ℝ), illustrative.InBox θ ∧ (∀ t, u t ≤ 0.40) ∧
      IsTrajectory illustrative θ u v 0 10 ∧ v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧
      v 2.16 < 1.35 ∧ ∀ t ∈ Icc (2.34 : ℝ) 10, 1.35 ≤ v t := by
  have hv₀ : (-0.10 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, htraj, hup⟩ := slow_rise_run (-0.10) hv₀
  refine ⟨slowUp, fun _ => 0.40, v, slowUp_inBox, fun _ => le_rfl, htraj,
    by rw [hv0]; norm_num, ?_, fun t ht => ?_⟩
  · have := hup 2.16 (by norm_num)
    norm_num at this ⊢
    linarith
  · have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
    have := htraj.rise_of_cert illustrative_admissible slowUp_inBox h0 illustrative_riseCert_3
      (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) t
      ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])
    simpa [illustrative] using this

/-- **No certificate can claim 2.16 ns or less.** Whatever list of levels is
proposed, `ValidRiseCert` with a deadline of 2.16 ns is refuted: a valid
certificate would force the slow run above to be valid-high at 2.16 ns. So the
certificate mechanism cannot be gamed below what the model allows. -/
theorem no_riseCert_at_2p16 (c : ℝ) (cs : List ℝ) : ¬ illustrative.ValidRiseCert c cs 2.16 := by
  intro hcert
  have hv₀ : (-0.10 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, htraj, hup⟩ := slow_rise_run (-0.10) hv₀
  have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
  have h1 := htraj.rise_of_cert illustrative_admissible slowUp_inBox h0 hcert
    (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) 2.16
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  have h2 := hup 2.16 (by norm_num)
  norm_num [illustrative] at h1 h2
  linarith

/-- **A 1.64 ns rise deadline is false even from a valid-low output.** -/
theorem rise_deadline_1p64_is_false_from_valid_low :
    ∃ (θ : Params) (u v : ℝ → ℝ), illustrative.InBox θ ∧ (∀ t, u t ≤ 0.40) ∧
      IsTrajectory illustrative θ u v 0 10 ∧ v 0 ≤ 0.25 ∧ v 1.64 < 1.35 := by
  have hv₀ : (0.25 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, htraj, hup⟩ := slow_rise_run 0.25 hv₀
  refine ⟨slowUp, fun _ => 0.40, v, slowUp_inBox, fun _ => le_rfl, htraj, hv0.le, ?_⟩
  have := hup 1.64 (by norm_num)
  norm_num at this ⊢
  linarith

/-! ## Slowest fall: weak pull-down corner -/

/-- Highest supply, weakest NMOS with the largest threshold, strongest PMOS
with the smallest threshold. -/
def slowDn : Params := ⟨1.98, 160, 120, 0.60, 0.45⟩

theorem slowDn_inBox : illustrative.InBox slowDn := by
  constructor <;> norm_num [illustrative, slowDn]

theorem Inet_slowDn_ge {x : ℝ} (h2 : x ≤ 2.08) : -37.76 ≤ Inet slowDn 1.25 x := by
  have e1 : psq ((1.98 : ℝ) - 1.25 - 0.45) = (1.98 - 1.25 - 0.45) ^ 2 :=
    psq_of_nonneg (by norm_num)
  have e3 : psq ((1.25 : ℝ) - 0.60) = (1.25 - 0.60) ^ 2 := psq_of_nonneg (by norm_num)
  have e4 := psq_nonneg ((1.25 : ℝ) - x - 0.60)
  have e2 : psq (x - 1.25 - 0.45) ≤ psq ((2.08 : ℝ) - 1.25 - 0.45) := psq_mono (by linarith)
  have e5 : psq ((2.08 : ℝ) - 1.25 - 0.45) = (2.08 - 1.25 - 0.45) ^ 2 :=
    psq_of_nonneg (by norm_num)
  rw [e5] at e2
  simp only [Inet, Ip, In, slowDn, e1, e3]
  nlinarith

/-- **A 1.0 ns fall deadline is false**: a trajectory in the box, valid-high
input, initial state in the safe domain, not valid-low at 1.0 ns. -/
theorem fall_deadline_1p0_is_false :
    ∃ (θ : Params) (u v : ℝ → ℝ), illustrative.InBox θ ∧ (∀ t, 1.25 ≤ u t) ∧
      IsTrajectory illustrative θ u v 0 10 ∧ v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧ 0.25 < v 1.0 := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (20 : ℝ) := by norm_num [illustrative]
  have hC2 : (20 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (2 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  have hv₀ : (2.08 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm slowDn_inBox hC1 (u := fun _ => 1.25)
    (w := fun _ => 2) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet slowDn 1.25 (v t) + 2) / 20) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative slowDn (fun _ => 1.25) v 0 10 :=
    IsTrajectory.of_ode (Cf := fun _ => 20) (w := fun _ => 2) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨slowDn, fun _ => 1.25, v, slowDn_inBox, fun _ => le_rfl, htraj,
    by rw [hv0]; norm_num, ?_⟩
  have hlow : ∀ t ∈ Icc (0 : ℝ) 10, 2.08 + -1.788 * t ≤ v t := by
    intro t ht
    refine image_le_of_deriv_right_le_deriv_boundary
      (f := fun t => 2.08 + -1.788 * t) (f' := fun _ => -1.788) (a := 0) (b := 10)
      (by fun_prop)
      (fun x _ => by
        have h := ((hasDerivAt_id x).const_mul (-1.788 : ℝ)).const_add 2.08
        simpa using h.hasDerivWithinAt)
      (B := v) (B' := fun t => (Inet slowDn 1.25 (v t) + 2) / 20) (by simp [hv0]) hcont hder
      (fun x hx => ?_) ht
    have hs := hsafe x (Ico_subset_Icc_self hx)
    have hhi : v x ≤ 2.08 := by
      have : -0.10 ≤ v x ∧ v x ≤ 2.08 := by simpa [Design.Safe, illustrative] using hs
      exact this.2
    have := Inet_slowDn_ge hhi
    show (-1.788 : ℝ) ≤ (Inet slowDn 1.25 (v x) + 2) / 20
    linarith
  have := hlow 1.0 (by norm_num)
  norm_num at this ⊢
  linarith

/-- A falling certificate for the instance (the library proves `fall_of_cert`
but never instantiates it): 1.51 ns instead of 2.57 ns. -/
theorem illustrative_fallCert_3 : illustrative.ValidFallCert 0.65 [0.45, 0.25] 1.51 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [FallSegs, finalLevel, fallTime, Design.dnSegs, Design.Idn, illustrative,
      psq_eq_ite]

/-! ## The header sentence about 38 ps -/

/-- Fast corner of the box. -/
def fastUp : Params := ⟨1.98, 240, 120, 0.45, 0.45⟩

theorem fastUp_inBox : illustrative.InBox fastUp := by
  constructor <;> norm_num [illustrative, fastUp]

theorem Inet_fastUp_ge {x : ℝ} (h1 : -0.10 ≤ x) (h2 : x ≤ 1.35) :
    (167.454 : ℝ) ≤ Inet fastUp (-1) x := by
  have e1 : psq ((1.98 : ℝ) - -1 - 0.45) = (1.98 - -1 - 0.45) ^ 2 := psq_of_nonneg (by norm_num)
  have e2 : psq (x - -1 - 0.45) = (x - -1 - 0.45) ^ 2 := psq_of_nonneg (by linarith)
  have e3 : psq ((-1 : ℝ) - 0.45) = 0 := psq_of_nonpos (by norm_num)
  have e4 : psq ((-1 : ℝ) - x - 0.45) = 0 := psq_of_nonpos (by linarith)
  simp only [Inet, Ip, In, fastUp, e1, e2, e3, e4]
  nlinarith

/-- **Valid-low input, valid-low initial output, valid-high output at 38 ps.**
The input is the constant `-1 V`, which is "valid-low" for the guarantee
(`u ≤ VIL`); parameters are in the box; the disturbance is zero. -/
theorem valid_low_input_can_give_valid_high_within_38ps :
    ∃ (θ : Params) (u v : ℝ → ℝ), illustrative.InBox θ ∧ (∀ t, u t ≤ 0.40) ∧ v 0 ≤ 0.25 ∧
      IsTrajectory illustrative θ u v 0 10 ∧ 1.35 ≤ v 0.038 := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (5 : ℝ) := by norm_num [illustrative]
  have hC2 : (5 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (0 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  have hv₀ : (0.25 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm fastUp_inBox hC1 (u := fun _ => -1)
    (w := fun _ => 0) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet fastUp (-1) (v t) + 0) / 5) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative fastUp (fun _ => -1) v 0 10 :=
    IsTrajectory.of_ode (Cf := fun _ => 5) (w := fun _ => 0) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨fastUp, fun _ => -1, v, fastUp_inBox, fun _ => by norm_num, hv0.le, htraj, ?_⟩
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

end Review.P03

#print axioms Review.P03.rise_deadline_2p16_is_false
#print axioms Review.P03.no_riseCert_at_2p16
#print axioms Review.P03.rise_deadline_1p64_is_false_from_valid_low
#print axioms Review.P03.fall_deadline_1p0_is_false
#print axioms Review.P03.illustrative_fallCert_3
#print axioms Review.P03.valid_low_input_can_give_valid_high_within_38ps
