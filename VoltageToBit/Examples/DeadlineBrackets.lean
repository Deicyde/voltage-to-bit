import VoltageToBit.Examples.Illustrative

/-!
# Deadline brackets for the illustrative instance

How tight are the proved deadlines? For each direction this file gives a
*bracket*: a deadline for which the claim of the guarantee is **false** (an
exhibited trajectory violates it) and a deadline for which it is **proved** for
every trajectory.

The claim in question is the one of `illustrative_guarantee`, with the deadline
`τ` as the only thing that changes. Rise: for every input and every trajectory
of the illustrative record that starts in the safe domain `[-0.10, 2.08]` V,
if the input is valid-low (`u ≤ 0.40` V) on `[s, e)` then the output is
valid-high (`v ≥ 1.35` V) on `[s + τ, e]`. Fall: the same with a valid-high
input (`u ≥ 1.25` V) and a valid-low output (`v ≤ 0.25` V).

| Direction | claim is false for | claim is proved for | statement |
| --- | --- | --- | --- |
| rise (low in, high out) | every `τ ≤ 2.16 ns` | every `τ ≥ 2.34 ns` | `rise_deadline_bracket` |
| fall (high in, low out) | every `τ ≤ 1.0 ns` | every `τ ≥ 1.51 ns` | `fall_deadline_bracket` |

A claim that is false for `τ` is false for every smaller `τ`, and a claim that
is proved for `τ` holds for every larger `τ`; the two bracket statements
include this. **Between the refuted and the proved value nothing is known from
these theorems**: a rise deadline strictly between 2.16 ns and 2.34 ns, or a
fall deadline strictly between 1.0 ns and 1.51 ns, is neither proved nor
refuted here. (The reviewer's numerical integration puts the slowest runs of
the model at about 2.25 ns and 1.39 ns. That is a numerical estimate, recorded
under finding E1-05 of `docs/adversarial-review.md`; it is not a Lean result.)

The two ends of each bracket are also stated on their own, the refutation as
an exhibited trajectory: `rise_deadline_2p16_is_false` and
`rise_deadline_2p34_holds`, `fall_deadline_1p0_is_false` and
`fall_deadline_1p51_holds`. All six statements carry their numbers in the
statements themselves.

Further statements:

* `no_riseCert_at_2p16`, `no_fallCert_at_1p0`: no list of levels whatsoever is
  a valid certificate for 2.16 ns (rising) or for 1.0 ns (falling). This is
  more than a rejected certificate: `illustrative_riseCert_rejected` (negative
  controls) only shows that one particular list fails a sufficient condition.
* `rise_deadline_1p64_is_false_from_valid_low`: even when the output starts
  valid-low (at 0.25 V) it need not be valid-high at 1.64 ns. No proved
  deadline is specific to that start; the general 2.34 ns applies, so for a
  valid-low start the bracket is 1.64 ns to 2.34 ns.
* `illustrative_fallCert_3`: a falling certificate. The library proves
  `IsTrajectory.fall_of_cert` for every list of levels; here it is
  instantiated. The certificate improves the fall deadline of
  `illustrative_guarantee` from 2.57 ns to 1.51 ns, as `illustrative_riseCert_3`
  improves the rise deadline from 3.43 ns to 2.34 ns.

The refuting trajectories are solutions of the node equation with constant
parameters, constant capacitance and constant disturbance (`slow_rise_run`,
`slow_fall_run`): they do not use the freedom of the inclusion to change the
parameter point or the capacitance from instant to instant.

* Rising: corner `slowUp` (lowest supply, weakest PMOS with the largest
  threshold), capacitance 20 fF, disturbance -2 µA, input held at 0.40 V,
  started at -0.10 V (at 0.25 V for the valid-low start).
* Falling: corner `slowDn` (highest supply, weakest NMOS with the largest
  threshold, strongest PMOS with the smallest threshold), capacitance 20 fF,
  disturbance +2 µA, input held at 1.25 V, started at 2.08 V.

Provenance. The content of this file was contributed by workstream E's review
probes (`review/P03_DeadlineBrackets.lean`, in the form ported to the
per-instant trajectory notion in `review/D05_Part1Ports.lean`; finding E1-05 of
`docs/adversarial-review.md`) and ported into the library. Added in the port:
the node equation as a conjunct of the two runs, `slow_fall_run` as a lemma of
its own, the last conjunct of `fall_deadline_1p0_is_false` (valid-low from
1.51 ns on), `no_fallCert_at_1p0`, and the statements
`rise_deadline_2p34_holds`, `fall_deadline_1p51_holds`,
`rise_deadline_bracket`, `fall_deadline_bracket`.
-/

namespace VoltageToBit.Examples

open Set

/-! ## Rising output -/

/-- A slow pull-up corner of the box: lowest supply, weakest PMOS with the
largest threshold. With `Vtn = 0.60` the NMOS is off on the whole safe domain
for the input 0.40 V used below, so `kn` plays no role. -/
def slowUp : Params := ⟨1.62, 240, 80, 0.60, 0.60⟩

theorem slowUp_inBox : illustrative.InBox slowUp := by
  constructor <;> norm_num [illustrative, slowUp]

/-- At the corner `slowUp` with the input at 0.40 V, the net current into a
node at or above -0.10 V is at most 15.376 µA. -/
theorem Inet_slowUp_le {x : ℝ} (h1 : -0.10 ≤ x) : Inet slowUp 0.40 x ≤ 15.376 := by
  have e1 : psq ((1.62 : ℝ) - 0.40 - 0.60) = (1.62 - 0.40 - 0.60) ^ 2 :=
    psq_of_nonneg (by norm_num)
  have e3 : psq ((0.40 : ℝ) - 0.60) = 0 := psq_of_nonpos (by norm_num)
  have e4 : psq ((0.40 : ℝ) - x - 0.60) = 0 := psq_of_nonpos (by linarith)
  have e2 := psq_nonneg (x - 0.40 - 0.60)
  simp only [Inet, Ip, In, slowUp, e1, e3, e4]
  nlinarith

/-- **A slow rising run** from the initial state `v₀`: the solution of the node
equation `20 * v' = Inet slowUp 0.40 v - 2` on `[0, 10]` (corner `slowUp`,
capacitance 20 fF, constant disturbance -2 µA, input held at 0.40 V). It
exists, it is a trajectory of the illustrative record, and it stays below the
line `v₀ + 0.6688 * t`. -/
theorem slow_rise_run (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 10,
        HasDerivWithinAt v ((Inet slowUp 0.40 (v t) + -2) / 20) (Icc 0 10) t) ∧
      IsTrajectory illustrative (fun _ => 0.40) v 0 10 ∧
      ∀ t ∈ Icc (0 : ℝ) 10, v t ≤ v₀ + 0.6688 * t := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (20 : ℝ) := by norm_num [illustrative]
  have hC2 : (20 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (-2 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm slowUp_inBox (Cf := fun _ => 20) (Kc := 0)
    (fun _ => hC1) (fun x _ y _ => by simp) (u := fun _ => 0.40)
    (w := fun _ => -2) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet slowUp 0.40 (v t) + -2) / 20) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => 0.40) v 0 10 :=
    IsTrajectory.of_ode slowUp_inBox (Cf := fun _ => 20) (w := fun _ => -2) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨v, hv0, hode, htraj, fun t ht => ?_⟩
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

/-- **A 2.16 ns rise deadline is false.** There is a trajectory of the
illustrative record with a valid-low input at all times and an initial state in
the safe domain that is not valid-high at 2.16 ns. On the very same trajectory
the output is valid-high from 2.34 ns on (certificate). The witness is
`slow_rise_run` started at -0.10 V. -/
theorem rise_deadline_2p16_is_false :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧
      IsTrajectory illustrative u v 0 10 ∧ v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧
      v 2.16 < 1.35 ∧ ∀ t ∈ Icc (2.34 : ℝ) 10, 1.35 ≤ v t := by
  have hv₀ : (-0.10 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hup⟩ := slow_rise_run (-0.10) hv₀
  refine ⟨fun _ => 0.40, v, fun _ => le_rfl, htraj,
    by rw [hv0]; norm_num, ?_, fun t ht => ?_⟩
  · have := hup 2.16 (by norm_num)
    norm_num at this ⊢
    linarith
  · have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
    have := htraj.rise_of_cert illustrative_admissible h0 illustrative_riseCert_3
      (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) t
      ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])
    simpa [illustrative] using this

/-- **No certificate can claim 2.16 ns.** Whatever list of levels is proposed,
`ValidRiseCert` with a deadline of 2.16 ns is refuted: a valid certificate
would force the slow run above to be valid-high at 2.16 ns. (A certificate
valid for a smaller deadline is valid for 2.16 ns as well, because validity
only asks that the summed segment times do not exceed the claimed deadline.)
So the certificate mechanism cannot be used to claim a deadline that the model
violates. -/
theorem no_riseCert_at_2p16 (c : ℝ) (cs : List ℝ) : ¬ illustrative.ValidRiseCert c cs 2.16 := by
  intro hcert
  have hv₀ : (-0.10 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hup⟩ := slow_rise_run (-0.10) hv₀
  have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
  have h1 := htraj.rise_of_cert illustrative_admissible h0 hcert
    (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) 2.16
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  have h2 := hup 2.16 (by norm_num)
  norm_num [illustrative] at h1 h2
  linarith

/-- **A 1.64 ns rise deadline is false even from a valid-low output.** The
witness is `slow_rise_run` started at 0.25 V. -/
theorem rise_deadline_1p64_is_false_from_valid_low :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧
      IsTrajectory illustrative u v 0 10 ∧ v 0 ≤ 0.25 ∧ v 1.64 < 1.35 := by
  have hv₀ : (0.25 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hup⟩ := slow_rise_run 0.25 hv₀
  refine ⟨fun _ => 0.40, v, fun _ => le_rfl, htraj, hv0.le, ?_⟩
  have := hup 1.64 (by norm_num)
  norm_num at this ⊢
  linarith

/-- **A 2.34 ns rise deadline is proved**, for every input and every trajectory
that starts in the safe domain: whenever `u ≤ 0.40` V on `[s, e)`, `v ≥ 1.35` V
on `[s + 2.34 ns, e]`. This is item 2 of `illustrative_guarantee` with 3.43 ns
replaced by 2.34 ns, obtained from the certificate `illustrative_riseCert_3`. -/
theorem rise_deadline_2p34_holds (u v : ℝ → ℝ) (a b : ℝ)
    (h : IsTrajectory illustrative u v a b) (h0 : v a ∈ Icc (-0.10 : ℝ) 2.08)
    (s e : ℝ) (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, u t ≤ 0.40) :
    ∀ t ∈ Icc s e, s + 2.34 ≤ t → 1.35 ≤ v t := by
  intro t ht htime
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  have h0' : v a ∈ illustrative.Safe := by rw [hsafe]; exact h0
  have := h.rise_of_cert illustrative_admissible h0' illustrative_riseCert_3 hs he
    (fun x hx => by simpa [illustrative] using hu x hx) t ht htime
  simpa [illustrative] using this

/-- **Rise bracket.** The rise claim of the guarantee with deadline `τ` (item 2
of `illustrative_guarantee`, with `τ` in place of 3.43 ns) is false for every
`τ ≤ 2.16` ns and true for every `τ ≥ 2.34` ns. For `2.16 < τ < 2.34` this
statement says nothing. -/
theorem rise_deadline_bracket (τ : ℝ) :
    (τ ≤ 2.16 → ¬ ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
          ∀ t ∈ Icc s e, s + τ ≤ t → 1.35 ≤ v t) ∧
    (2.34 ≤ τ → ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
          ∀ t ∈ Icc s e, s + τ ≤ t → 1.35 ≤ v t) := by
  refine ⟨fun hτ hall => ?_, fun hτ u v a b h h0 s e hs he hu t ht htime =>
    rise_deadline_2p34_holds u v a b h h0 s e hs he hu t ht (by linarith)⟩
  obtain ⟨u, v, hu, htraj, h0, hlt, -⟩ := rise_deadline_2p16_is_false
  have := hall u v 0 10 htraj h0 0 10 le_rfl le_rfl (fun t _ => hu t) 2.16
    ⟨by norm_num, by norm_num⟩ (by linarith)
  linarith

/-! ## Falling output -/

/-- A slow pull-down corner of the box: highest supply, weakest NMOS with the
largest threshold, strongest PMOS with the smallest threshold. -/
def slowDn : Params := ⟨1.98, 160, 120, 0.60, 0.45⟩

theorem slowDn_inBox : illustrative.InBox slowDn := by
  constructor <;> norm_num [illustrative, slowDn]

/-- At the corner `slowDn` with the input at 1.25 V, the net current out of a
node at or below 2.08 V is at most 37.76 µA. -/
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

/-- **A slow falling run** from the initial state `v₀`: the solution of the
node equation `20 * v' = Inet slowDn 1.25 v + 2` on `[0, 10]` (corner `slowDn`,
capacitance 20 fF, constant disturbance +2 µA, input held at 1.25 V). It
exists, it is a trajectory of the illustrative record, and it stays above the
line `v₀ - 1.788 * t`. -/
theorem slow_fall_run (v₀ : ℝ) (hv₀ : v₀ ∈ illustrative.Safe) :
    ∃ v : ℝ → ℝ, v 0 = v₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 10,
        HasDerivWithinAt v ((Inet slowDn 1.25 (v t) + 2) / 20) (Icc 0 10) t) ∧
      IsTrajectory illustrative (fun _ => 1.25) v 0 10 ∧
      ∀ t ∈ Icc (0 : ℝ) 10, v₀ + -1.788 * t ≤ v t := by
  have hadm := illustrative_admissible
  have hC1 : illustrative.Clo ≤ (20 : ℝ) := by norm_num [illustrative]
  have hC2 : (20 : ℝ) ≤ illustrative.Chi := by norm_num [illustrative]
  have hwb : ∀ t ∈ Icc (0 : ℝ) 10, |(fun _ : ℝ => (2 : ℝ)) t| ≤ illustrative.eps :=
    fun t _ => by norm_num [illustrative]
  obtain ⟨v, hv0, hsafe, hode⟩ := exists_solution hadm slowDn_inBox (Cf := fun _ => 20) (Kc := 0)
    (fun _ => hC1) (fun x _ y _ => by simp) (u := fun _ => 1.25)
    (w := fun _ => 2) continuous_const continuous_const (by norm_num : (0 : ℝ) ≤ 10) hwb hv₀
  have hder : ∀ t ∈ Ico (0 : ℝ) 10,
      HasDerivWithinAt v ((Inet slowDn 1.25 (v t) + 2) / 20) (Ici t) t :=
    fun t ht => (hode t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn v (Icc 0 10) := fun t ht => (hode t ht).continuousWithinAt
  have htraj : IsTrajectory illustrative (fun _ => 1.25) v 0 10 :=
    IsTrajectory.of_ode slowDn_inBox (Cf := fun _ => 20) (w := fun _ => 2) (fun _ => ⟨hC1, hC2⟩)
      (fun t ht => hwb t (Ico_subset_Icc_self ht)) hcont
      (fun t ht => ⟨_, hder t ht, by field_simp⟩)
  refine ⟨v, hv0, hode, htraj, fun t ht => ?_⟩
  refine image_le_of_deriv_right_le_deriv_boundary
    (f := fun t => v₀ + -1.788 * t) (f' := fun _ => -1.788) (a := 0) (b := 10)
    (by fun_prop)
    (fun x _ => by
      have h := ((hasDerivAt_id x).const_mul (-1.788 : ℝ)).const_add v₀
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

/-- A falling certificate for the instance: three levels improve the fall
deadline from 2.57 ns to 1.51 ns under exactly the same assumptions. -/
theorem illustrative_fallCert_3 : illustrative.ValidFallCert 0.65 [0.45, 0.25] 1.51 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [FallSegs, finalLevel, fallTime, Design.dnSegs, Design.Idn, illustrative,
      psq_eq_ite]

/-- **A 1.0 ns fall deadline is false.** There is a trajectory of the
illustrative record with a valid-high input at all times and an initial state
in the safe domain that is not valid-low at 1.0 ns. On the very same trajectory
the output is valid-low from 1.51 ns on (certificate). The witness is
`slow_fall_run` started at 2.08 V. -/
theorem fall_deadline_1p0_is_false :
    ∃ u v : ℝ → ℝ, (∀ t, 1.25 ≤ u t) ∧
      IsTrajectory illustrative u v 0 10 ∧ v 0 ∈ Icc (-0.10 : ℝ) 2.08 ∧
      0.25 < v 1.0 ∧ ∀ t ∈ Icc (1.51 : ℝ) 10, v t ≤ 0.25 := by
  have hv₀ : (2.08 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hlow⟩ := slow_fall_run 2.08 hv₀
  refine ⟨fun _ => 1.25, v, fun _ => le_rfl, htraj, by rw [hv0]; norm_num, ?_, fun t ht => ?_⟩
  · have := hlow 1.0 (by norm_num)
    norm_num at this ⊢
    linarith
  · have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
    have := htraj.fall_of_cert illustrative_admissible h0 illustrative_fallCert_3
      (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) t
      ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])
    simpa [illustrative] using this

/-- **No certificate can claim 1.0 ns.** Whatever list of levels is proposed,
`ValidFallCert` with a deadline of 1.0 ns is refuted: a valid certificate would
force the slow run above to be valid-low at 1.0 ns. -/
theorem no_fallCert_at_1p0 (c : ℝ) (cs : List ℝ) : ¬ illustrative.ValidFallCert c cs 1.0 := by
  intro hcert
  have hv₀ : (2.08 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hlow⟩ := slow_fall_run 2.08 hv₀
  have h0 : v 0 ∈ illustrative.Safe := by rw [hv0]; exact hv₀
  have h1 := htraj.fall_of_cert illustrative_admissible h0 hcert
    (s := 0) (e := 10) le_rfl le_rfl (fun _ _ => by norm_num [illustrative]) 1.0
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  have h2 := hlow 1.0 (by norm_num)
  norm_num [illustrative] at h1 h2
  linarith

/-- **A 1.51 ns fall deadline is proved**, for every input and every trajectory
that starts in the safe domain: whenever `u ≥ 1.25` V on `[s, e)`, `v ≤ 0.25` V
on `[s + 1.51 ns, e]`. This is item 3 of `illustrative_guarantee` with 2.57 ns
replaced by 1.51 ns, obtained from the certificate `illustrative_fallCert_3`. -/
theorem fall_deadline_1p51_holds (u v : ℝ → ℝ) (a b : ℝ)
    (h : IsTrajectory illustrative u v a b) (h0 : v a ∈ Icc (-0.10 : ℝ) 2.08)
    (s e : ℝ) (hs : a ≤ s) (he : e ≤ b) (hu : ∀ t ∈ Ico s e, 1.25 ≤ u t) :
    ∀ t ∈ Icc s e, s + 1.51 ≤ t → v t ≤ 0.25 := by
  intro t ht htime
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  have h0' : v a ∈ illustrative.Safe := by rw [hsafe]; exact h0
  have := h.fall_of_cert illustrative_admissible h0' illustrative_fallCert_3 hs he
    (fun x hx => by simpa [illustrative] using hu x hx) t ht htime
  simpa [illustrative] using this

/-- **Fall bracket.** The fall claim of the guarantee with deadline `τ` (item 3
of `illustrative_guarantee`, with `τ` in place of 2.57 ns) is false for every
`τ ≤ 1.0` ns and true for every `τ ≥ 1.51` ns. For `1.0 < τ < 1.51` this
statement says nothing. -/
theorem fall_deadline_bracket (τ : ℝ) :
    (τ ≤ 1.0 → ¬ ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
          ∀ t ∈ Icc s e, s + τ ≤ t → v t ≤ 0.25) ∧
    (1.51 ≤ τ → ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
          ∀ t ∈ Icc s e, s + τ ≤ t → v t ≤ 0.25) := by
  refine ⟨fun hτ hall => ?_, fun hτ u v a b h h0 s e hs he hu t ht htime =>
    fall_deadline_1p51_holds u v a b h h0 s e hs he hu t ht (by linarith)⟩
  obtain ⟨u, v, hu, htraj, h0, hgt, -⟩ := fall_deadline_1p0_is_false
  have := hall u v 0 10 htraj h0 0 10 le_rfl le_rfl (fun t _ => hu t) 1.0
    ⟨by norm_num, by norm_num⟩ (by linarith)
  linarith

end VoltageToBit.Examples
