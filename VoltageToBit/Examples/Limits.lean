import VoltageToBit.Examples.Illustrative

/-!
# Limits for the illustrative inverter: how far any proposal can go

None of the statements here improves the guarantee. They say where improvement
stops.

| Quantity | Refuted below | Statement | Proved at |
| --- | --- | --- | --- |
| Rise deadline | 2.168 ns | `rise_deadline_counterexample` | 2.26 ns |
| Fall deadline | 1.0234 ns | `fall_deadline_counterexample` | 1.425 ns |

The proved values are those of `Examples/RefinedDeadlines.lean`
(`illustrative_guarantee_refined`). For a deadline at or above the refuted
value and below the proved value the library has no statement in either
direction. `Examples/DeadlineBrackets.lean` puts the two ends of each row into
one statement and says what each end means. The numerical experiments
(`docs/discrepancy-report.md`, section 2) observed worst-case delays of about
2.2512 ns (rise) and 1.3945 ns (fall). Those two numbers are observations of a
simulation of the model, not theorems.

This file is the one place where the slow corners and the slow runs are
defined; the other example files use them from here.

* `slowUpCorner`, `slowDnCorner`: the two slow corners of the parameter box.
* `slow_rise_run`, `slow_fall_run`: the slow runs. For every initial state in
  the safe domain there is a solution on `[0, 10]` of the node equation at the
  slow corner, with the largest capacitance (20 fF), the input held at the edge
  of its valid band and the disturbance held at its adverse bound. Its
  existence is proved, not assumed. The statement contains the node equation,
  so the run is visibly one with constant parameters, constant capacitance and
  constant disturbance: it does not use the freedom of the inclusion to change
  the parameter point or the capacitance from instant to instant. The run is a
  trajectory of the illustrative record and stays on the slow side of an
  explicit line.
* `rise_deadline_counterexample`, `fall_deadline_counterexample`: every
  deadline below 2.168 ns (rise) or 1.0234 ns (fall) is violated by the slow
  run started at the far end of the safe domain (-0.10 V, 2.08 V).
* `riseCert_deadline_ge`, `fallCert_deadline_ge`: hence no certificate, whoever
  proposes it, can claim a smaller deadline.
* `illustrativeEps`, `illustrativeEps_admissible`: the same circuit is admissible
  with `eps = 2.3801` µA once the proof-only split points are re-chosen. This is
  a different claim from the `eps = 2` guarantee (more trajectories, longer
  closed-form deadlines), not an improvement of it.
* `illustrative_eps_no_split_points`: for `eps ≥ 2.3802` µA no choice of split
  points makes the record admissible. This is a limit of the one-transistor
  boundary bound used in `Design.Admissible`, not a statement that the circuit
  fails: numerically the model's smallest restoring current is about 5.9 µA at
  the bottom of the safe domain and 6.4 µA at the top.

Provenance. The statements were produced by workstream F's search loop
(`docs/experiment-loop.md`, `search/promote/Limits.lean`) and ported to the
current shape of the library by the coordinator. The same two slow runs are
used in workstream E's review probes (`review/P03_DeadlineBrackets.lean`, in
the form of `review/D05_Part1Ports.lean`; finding E1-05 of
`docs/adversarial-review.md`). The two versions are merged here:
`slow_rise_run` and `slow_fall_run` are stated for every initial state in the
safe domain and include the node equation, and the runs from -0.10 V and from
2.08 V that the search loop recorded as `slow_rise_trajectory` and
`slow_fall_trajectory` are their instances at those two initial states.
-/

namespace VoltageToBit.Examples

open Set

/-- A signal whose right derivative is at most `m` stays below the line of
slope `m` through its initial bound. -/
theorem le_line_of_rderiv_le {v v' : ℝ → ℝ} {a b l m : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (hl : v a ≤ l) (hm : ∀ t ∈ Ico a b, v' t ≤ m) :
    ∀ t ∈ Icc a b, v t ≤ l + m * (t - a) := by
  intro t ht
  refine image_le_of_deriv_right_le_deriv_boundary (f := v) (f' := v') hv hv'
    (B := fun x => l + m * (x - a)) (B' := fun _ => m) (by simpa using hl) (by fun_prop)
    (fun x _ => by
      have hd := (((hasDerivAt_id x).sub_const a).const_mul m).const_add l
      simpa using hd.hasDerivWithinAt)
    hm ht

/-! ## Rising output -/

/-- Slow pull-up corner of the box: lowest supply, weakest PMOS with the
largest threshold magnitude, NMOS with the largest threshold. With
`Vtn = 0.60` the NMOS is off on the whole safe domain for the input 0.40 V
used below, so `kn` plays no role. -/
def slowUpCorner : Params := ⟨1.62, 240, 80, 0.60, 0.60⟩

theorem slowUpCorner_inBox : illustrative.InBox slowUpCorner := by
  constructor <;> norm_num [illustrative, slowUpCorner]

/-- At the slow pull-up corner with the input at `VIL = 0.40` V the devices
deliver at most 15.376 µA into a node at or above `-0.10` V. -/
theorem Inet_slowUp_le {x : ℝ} (hx : (-0.10 : ℝ) ≤ x) :
    Inet slowUpCorner 0.40 x ≤ 15.376 := by
  have h1 : Ip slowUpCorner 0.40 x
      ≤ slowUpCorner.kp / 2 * psq (slowUpCorner.VDD - 0.40 - slowUpCorner.Vtp) :=
    Ip_le_sat (by norm_num [slowUpCorner])
  have h2 : In slowUpCorner 0.40 x = 0 := by
    unfold In
    rw [psq_of_nonpos (by norm_num [slowUpCorner]),
      psq_of_nonpos (by norm_num [slowUpCorner]; linarith)]
    ring
  have h3 : slowUpCorner.kp / 2 * psq (slowUpCorner.VDD - 0.40 - slowUpCorner.Vtp) = 15.376 := by
    norm_num [slowUpCorner, psq_eq_ite]
  unfold Inet
  linarith

/-- **A slow rising run** from the initial state `v₀`, for every `v₀` in the
safe domain: the solution of the node equation
`20 * v' = Inet slowUpCorner 0.40 v - 2` on `[0, 10]` (corner `slowUpCorner`,
capacitance 20 fF, the input held at 0.40 V, which is valid-low, and the
disturbance held at -2 µA). It exists, it is a trajectory of the illustrative
record, and it stays below the line `v₀ + 0.6688 * t`
(`0.6688 = (15.376 - 2) / 20`, see `Inet_slowUp_le`). -/
theorem slow_rise_run (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 10,
        HasDerivWithinAt v ((Inet slowUpCorner 0.40 (v t) + -2) / 20) (Icc 0 10) t) ∧
      IsTrajectory illustrative (fun _ => 0.40) v 0 10 ∧
      ∀ t ∈ Icc (0 : ℝ) 10, v t ≤ v₀ + 0.6688 * t := by
  have hC1 : illustrative.Clo ≤ (20 : ℝ) := by norm_num [illustrative]
  have hC2 : (20 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (-2 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution illustrative_admissible slowUpCorner_inBox
    (Cf := fun _ => 20) (Kc := 0) (fun _ => hC1) (fun x _ y _ => by simp)
    (u := fun _ => (0.40 : ℝ)) (w := fun _ => (-2 : ℝ)) continuous_const continuous_const
    (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet slowUpCorner 0.40 (v t) + -2) / 20) (Ici t) t := fun t ht =>
    (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => 0.40) v 0 10 :=
    IsTrajectory.of_ode slowUpCorner_inBox (Cf := fun _ => 20) (w := fun _ => (-2 : ℝ))
      (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨v, hv0, hode, htraj, fun t ht => ?_⟩
  have hslope : ∀ s ∈ Ico (0 : ℝ) 10, (Inet slowUpCorner 0.40 (v s) + -2) / 20 ≤ 0.6688 := by
    intro s hs
    have hvs : (-0.10 : ℝ) ≤ v s := by
      have := (hsafe s (Ico_subset_Icc_self hs)).1
      simpa [illustrative] using this
    have := Inet_slowUp_le hvs
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have := le_line_of_rderiv_le hcont hder hv0.le hslope t ht
  linarith

/-- **No rise deadline below 2.168 ns is valid** for the illustrative record:
for every such `τ` there are a valid-low input, a trajectory starting in the
safe domain and a time `t ≥ τ` at which the output is still below `VOH`. The
witness is `slow_rise_run` started at -0.10 V, the bottom of the safe domain.

The number 2.168 is rounded down: the line bound of that run reaches 1.35 V at
`1.45 / 0.6688 ≈ 2.16806` ns. -/
theorem rise_deadline_counterexample {τ : ℝ} (hτ : τ < 2.168) :
    ∃ (u v : ℝ → ℝ) (t : ℝ),
      IsTrajectory illustrative u v 0 10 ∧ v 0 ∈ illustrative.Safe ∧
      (∀ s ∈ Ico (0 : ℝ) 10, u s ≤ illustrative.VIL) ∧
      t ∈ Icc (0 : ℝ) 10 ∧ 0 + τ ≤ t ∧ v t < illustrative.VOH := by
  have hv₀ : (-0.10 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hbound⟩ := slow_rise_run (-0.10) hv₀
  have ht : max τ 0 ∈ Icc (0 : ℝ) 10 := ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩
  refine ⟨fun _ => 0.40, v, max τ 0, htraj, ?_, ?_, ht, ?_, ?_⟩
  · rw [hv0]; exact hv₀
  · intro s _; norm_num [illustrative]
  · simp
  · have hb := hbound (max τ 0) ht
    have hlt : max τ 0 < 2.168 := max_lt hτ (by norm_num)
    have : illustrative.VOH = 1.35 := by norm_num [illustrative]
    rw [this]
    nlinarith

/-- **No certificate can prove a rise deadline below 2.168 ns.** Whatever list
of levels is proposed, `ValidRiseCert` with a deadline `τ` forces `2.168 ≤ τ`:
a valid certificate with a smaller deadline would force the slow run above to
be valid-high too early. So the certificate mechanism cannot be used to claim a
deadline that the model violates. -/
theorem riseCert_deadline_ge {c : ℝ} {cs : List ℝ} {τ : ℝ}
    (h : illustrative.ValidRiseCert c cs τ) : 2.168 ≤ τ := by
  by_contra hlt
  obtain ⟨u, v, t, htraj, h0, hu, ht, hτt, hv⟩ :=
    rise_deadline_counterexample (not_le.mp hlt)
  have := htraj.rise_of_cert illustrative_admissible h0 h le_rfl le_rfl hu t ht hτt
  linarith

/-! ## Falling output -/

/-- A signal whose right derivative is at least `-m` stays above the line of
slope `-m` through its initial bound. -/
theorem ge_line_of_rderiv_ge {v v' : ℝ → ℝ} {a b h m : ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hv' : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (hh : h ≤ v a) (hm : ∀ t ∈ Ico a b, -m ≤ v' t) :
    ∀ t ∈ Icc a b, h - m * (t - a) ≤ v t := by
  intro t ht
  refine image_le_of_deriv_right_le_deriv_boundary
    (f := fun x => h - m * (x - a)) (f' := fun _ => -m) (by fun_prop)
    (fun x _ => by
      have hd := (((hasDerivAt_id x).sub_const a).const_mul m).const_sub h
      simpa using hd.hasDerivWithinAt)
    (B := v) (B' := v') (by simpa using hh) hv hv' hm ht

/-- Slow pull-down corner of the box: weakest NMOS with the largest threshold,
strongest PMOS with the smallest threshold magnitude at the highest supply. -/
def slowDnCorner : Params := ⟨1.98, 160, 120, 0.60, 0.45⟩

theorem slowDnCorner_inBox : illustrative.InBox slowDnCorner := by
  constructor <;> norm_num [illustrative, slowDnCorner]

/-- At the slow pull-down corner with the input at `VIH = 1.25` V the devices
remove at most 37.76 µA from a node at or below `2.08` V. -/
theorem Inet_slowDn_ge {x : ℝ} (hx : x ≤ (2.08 : ℝ)) :
    -37.76 ≤ Inet slowDnCorner 1.25 x := by
  have h1 : In slowDnCorner 1.25 x ≤ slowDnCorner.kn / 2 * psq (1.25 - slowDnCorner.Vtn) :=
    In_le_sat (by norm_num [slowDnCorner])
  have h2 : slowDnCorner.kn / 2 * psq (1.25 - slowDnCorner.Vtn) = 33.8 := by
    norm_num [slowDnCorner, psq_eq_ite]
  have h3 : psq (x - 1.25 - 0.45) ≤ psq (2.08 - 1.25 - 0.45) := psq_mono (by linarith)
  have h4 : psq (2.08 - 1.25 - 0.45 : ℝ) = 0.1444 := by norm_num [psq_eq_ite]
  have h5 : psq (1.98 - 1.25 - 0.45 : ℝ) = 0.0784 := by norm_num [psq_eq_ite]
  have h6 : Ip slowDnCorner 1.25 x
      = 60 * (psq (1.98 - 1.25 - 0.45) - psq (x - 1.25 - 0.45)) := by
    unfold Ip
    norm_num [slowDnCorner]
  unfold Inet
  rw [h6, h5]
  linarith

/-- **A slow falling run** from the initial state `v₀`, for every `v₀` in the
safe domain: the solution of the node equation
`20 * v' = Inet slowDnCorner 1.25 v + 2` on `[0, 10]` (corner `slowDnCorner`,
capacitance 20 fF, the input held at 1.25 V, which is valid-high, and the
disturbance held at +2 µA). It exists, it is a trajectory of the illustrative
record, and it stays above the line `v₀ - 1.788 * t`
(`1.788 = (37.76 - 2) / 20`, see `Inet_slowDn_ge`). -/
theorem slow_fall_run (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 10,
        HasDerivWithinAt v ((Inet slowDnCorner 1.25 (v t) + 2) / 20) (Icc 0 10) t) ∧
      IsTrajectory illustrative (fun _ => 1.25) v 0 10 ∧
      ∀ t ∈ Icc (0 : ℝ) 10, v₀ + -1.788 * t ≤ v t := by
  have hC1 : illustrative.Clo ≤ (20 : ℝ) := by norm_num [illustrative]
  have hC2 : (20 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (2 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution illustrative_admissible slowDnCorner_inBox
    (Cf := fun _ => 20) (Kc := 0) (fun _ => hC1) (fun x _ y _ => by simp)
    (u := fun _ => (1.25 : ℝ)) (w := fun _ => (2 : ℝ)) continuous_const continuous_const
    (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet slowDnCorner 1.25 (v t) + 2) / 20) (Ici t) t := fun t ht =>
    (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => 1.25) v 0 10 :=
    IsTrajectory.of_ode slowDnCorner_inBox (Cf := fun _ => 20) (w := fun _ => (2 : ℝ))
      (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨v, hv0, hode, htraj, fun t ht => ?_⟩
  have hslope : ∀ s ∈ Ico (0 : ℝ) 10, -1.788 ≤ (Inet slowDnCorner 1.25 (v s) + 2) / 20 := by
    intro s hs
    have hvs : v s ≤ (2.08 : ℝ) := by
      have := (hsafe s (Ico_subset_Icc_self hs)).2
      simpa [illustrative] using this
    have := Inet_slowDn_ge hvs
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have := ge_line_of_rderiv_ge hcont hder hv0.ge hslope t ht
  linarith

/-- **No fall deadline below 1.0234 ns is valid** for the illustrative record:
for every such `τ` there are a valid-high input, a trajectory starting in the
safe domain and a time `t ≥ τ` at which the output is still above `VOL`. The
witness is `slow_fall_run` started at 2.08 V, the top of the safe domain.

The number 1.0234 is rounded down: the line bound of that run reaches 0.25 V
at `1.83 / 1.788 ≈ 1.02349` ns. -/
theorem fall_deadline_counterexample {τ : ℝ} (hτ : τ < 1.0234) :
    ∃ (u v : ℝ → ℝ) (t : ℝ),
      IsTrajectory illustrative u v 0 10 ∧ v 0 ∈ illustrative.Safe ∧
      (∀ s ∈ Ico (0 : ℝ) 10, illustrative.VIH ≤ u s) ∧
      t ∈ Icc (0 : ℝ) 10 ∧ 0 + τ ≤ t ∧ illustrative.VOL < v t := by
  have hv₀ : (2.08 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hbound⟩ := slow_fall_run 2.08 hv₀
  have ht : max τ 0 ∈ Icc (0 : ℝ) 10 := ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩
  refine ⟨fun _ => 1.25, v, max τ 0, htraj, ?_, ?_, ht, ?_, ?_⟩
  · rw [hv0]; exact hv₀
  · intro s _; norm_num [illustrative]
  · simp
  · have hb := hbound (max τ 0) ht
    have hlt : max τ 0 < 1.0234 := max_lt hτ (by norm_num)
    have : illustrative.VOL = 0.25 := by norm_num [illustrative]
    rw [this]
    nlinarith

/-- **No certificate can prove a fall deadline below 1.0234 ns.** Whatever list
of levels is proposed, `ValidFallCert` with a deadline `τ` forces
`1.0234 ≤ τ`. -/
theorem fallCert_deadline_ge {c : ℝ} {cs : List ℝ} {τ : ℝ}
    (h : illustrative.ValidFallCert c cs τ) : 1.0234 ≤ τ := by
  by_contra hlt
  obtain ⟨u, v, t, htraj, h0, hu, ht, hτt, hv⟩ :=
    fall_deadline_counterexample (not_le.mp hlt)
  have := htraj.fall_of_cert illustrative_admissible h0 h le_rfl le_rfl hu t ht hτt
  linarith

/-! ## The disturbance bound -/

/-- The illustrative record with the largest disturbance bound found for which
admissibility is provable by changing only `uHi` and `uLo` (record `eps-006-split-search-6dp`). -/
noncomputable def illustrativeEps : Design :=
  { illustrative with eps := 2.3801, uHi := 0.772486, uLo := 0.742506 }

theorem illustrativeEps_admissible : illustrativeEps.Admissible := by
  constructor <;>
    norm_num [illustrativeEps, illustrative, Design.Iup, Design.Idn, Design.RhiP, Design.RhiN,
      Design.RloN, Design.RloP, psq_eq_ite]

/-- The price of the larger bound: longer closed-form deadlines. -/
theorem illustrativeEps_tauUp : illustrativeEps.tauUp = 290000 / 80959 := by
  norm_num [illustrativeEps, illustrative, Design.tauUp, Design.Iup, psq_eq_ite]

theorem illustrativeEps_tauDn : illustrativeEps.tauDn = 366000 / 139159 := by
  norm_num [illustrativeEps, illustrative, Design.tauDn, Design.Idn, psq_eq_ite]

/-- **No choice of the split points helps.** Once `eps ≥ 2.3802`, the record is
inadmissible for every `uHi` and `uLo`: for `uHi ≤ 0.77248` the NMOS-branch margin
`RhiN` is too small, and for `uHi ≥ 0.77248` the PMOS-branch margin `RhiP` is. -/
theorem illustrative_eps_no_split_points (e x y : ℝ) (he : 2.3802 ≤ e) :
    ¬ ({ illustrative with eps := e, uHi := x, uLo := y } : Design).Admissible := by
  intro h
  have hP := h.hiP
  have hN := h.hiN
  simp only [Design.RhiP, Design.RhiN, illustrative] at hP hN
  rcases le_total x 0.77248 with hx | hx
  · have h1 : psq (x - 0.60) ≤ psq (0.77248 - 0.60) := psq_mono (by linarith)
    have h2 := psq_nonneg (x - 2.08 - 0.60)
    have h3 : psq (0.77248 - 0.60 : ℝ) = 0.0297493504 := by norm_num [psq_eq_ite]
    rw [h3] at h1
    linarith
  · have h1 := psq_incr_mono (d := (2.08 - 1.98 : ℝ)) (x := 1.62 - x - 0.60)
      (y := 1.62 - 0.77248 - 0.60) (by norm_num) (by linarith)
    have h3 : psq (1.62 - 0.77248 - 0.60 + (2.08 - 1.98) : ℝ)
        - psq (1.62 - 0.77248 - 0.60) = 0.059504 := by
      norm_num [psq_eq_ite]
    rw [h3] at h1
    linarith

end VoltageToBit.Examples
