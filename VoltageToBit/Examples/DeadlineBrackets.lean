import VoltageToBit.Examples.Limits
import VoltageToBit.Examples.RefinedDeadlines

/-!
# Deadline brackets for the illustrative instance

How tight are the proved deadlines? For each direction this file puts the two
ends of the answer into one statement, a *bracket*: the deadlines for which the
claim of the guarantee is **false**, and the deadlines for which it is
**proved** for every trajectory. The brackets prove nothing new: the false
ends come from `Examples/Limits.lean` and the proved ends from
`Examples/RefinedDeadlines.lean`.

The claim in question is the one of `illustrative_guarantee`, with the deadline
`τ` as the only thing that changes. Rise: for every input and every trajectory
of the illustrative record that starts in the safe domain `[-0.10, 2.08]` V,
if the input is valid-low (`u ≤ 0.40` V) on `[s, e)` then the output is
valid-high (`v ≥ 1.35` V) on `[s + τ, e]`. Fall: the same with a valid-high
input (`u ≥ 1.25` V) and a valid-low output (`v ≤ 0.25` V).

| Direction | claim is false for | claim is proved for | statement |
| --- | --- | --- | --- |
| rise (low in, high out) | every `τ < 2.168 ns` | every `τ ≥ 2.26 ns` | `rise_deadline_bracket` |
| fall (high in, low out) | every `τ < 1.0234 ns` | every `τ ≥ 1.425 ns` | `fall_deadline_bracket` |

## What each end means

* **False for `τ`.** The claim speaks about every input and every trajectory,
  and it has a counterexample: an input that is valid throughout and a
  trajectory that starts in the safe domain whose output is still not valid at
  some time `t ≥ τ`. The counterexamples are the slow runs of
  `Examples/Limits.lean`, `slow_rise_run` started at -0.10 V and
  `slow_fall_run` started at 2.08 V, used through
  `rise_deadline_counterexample` and `fall_deadline_counterexample`. They are
  solutions of the node equation with constant parameters, constant
  capacitance and constant disturbance, and they start in the safe domain. A
  claim that is false for `τ` is false for every smaller `τ`.
* **Proved for `τ`.** The claim holds for every input function and every
  trajectory that starts in the safe domain. This comes from the two 16-level
  certificates of `Examples/RefinedDeadlines.lean`
  (`illustrative_guarantee_refined`). A claim that is proved for `τ` holds for
  every larger `τ`.

## What lies between the ends

For `2.168 ≤ τ < 2.26` (rise) and for `1.0234 ≤ τ < 1.425` (fall) **the library
has no statement in either direction**: no theorem says that such a deadline
is false and no theorem says that it holds. The two bracket statements say
nothing there.

The four ends are rounded numbers, not sharp limits of the two methods. The
slow runs refute a little more than the stated false ends: their line bounds
reach the output thresholds only at about 2.16806 ns and 1.02349 ns (see
`rise_deadline_counterexample` and `fall_deadline_counterexample`). And the
search record cited in `Examples/RefinedDeadlines.lean` lists 64-level
certificates for 2.2533 ns and 1.4193 ns. Neither refinement is stated in the
library, and neither would close the gaps, which are about 0.09 ns (rise) and
0.40 ns (fall) wide.

Simulation, not theorem. The numerical experiments
(`docs/discrepancy-report.md`, section 2) observed worst-case delays of about
2.2512 ns (rise) and 1.3945 ns (fall). Both numbers lie inside the gaps. They
are observations of a simulation of the model. They are not theorems, no
statement of the library depends on them, and they are not measurements of a
device.

## A start at the valid-low level

`rise_deadline_1p64_is_false_from_valid_low`: a start at 0.25 V, the highest
valid-low output level, instead of -0.10 V does not rescue a short deadline.
The slow rising run from 0.25 V is not valid-high at 1.64 ns. The statement
fixes the start, `v 0 = 0.25`. (`IsTrajectory` asks for the current balance
only while the node is in the safe domain, so an existence statement that does
not place the start there can be met by a function that stays outside it and
then shows nothing.) The library proves no deadline that is specific to this
start; the general 2.26 ns applies. So for a start at 0.25 V: one run with a
valid-low input is not valid-high at 1.64 ns, every trajectory with a
valid-low input is valid-high from 2.26 ns on, and nothing is stated in
between.

Provenance. Bracketing each deadline goes back to workstream E's review probes
(`review/P03_DeadlineBrackets.lean`, in the form of
`review/D05_Part1Ports.lean`; finding E1-05 of `docs/adversarial-review.md`).
The probes refute 2.16 ns (rise) and 1.0 ns (fall) and prove 2.34 ns and
1.51 ns with three-level certificates. An earlier version of this file stated
the brackets with those ends and had its own copies of the slow corners and
runs. Its statements follow from the ones kept now: the runs that are not yet
valid at 2.16 ns and at 1.0 ns from `slow_rise_run` and `slow_fall_run`, "no
certificate for 2.16 ns" and "no certificate for 1.0 ns" from
`riseCert_deadline_ge` and `fallCert_deadline_ge`, and the deadlines 2.34 ns
and 1.51 ns from `illustrative_guarantee_refined`. The three-level falling
certificate itself (levels 0.65, 0.45, 0.25 V for 1.51 ns) is no longer
stated; the 16-level certificate for 1.425 ns takes its place.
-/

namespace VoltageToBit.Examples

open Set

/-- **Rise bracket.** The rise claim of the guarantee with deadline `τ` (item 2
of `illustrative_guarantee`, with `τ` in place of 3.43 ns) is false for every
`τ < 2.168` ns and true for every `τ ≥ 2.26` ns. For `2.168 ≤ τ < 2.26` this
statement says nothing, and no other statement of the library decides the
claim.

The false end is `rise_deadline_counterexample` (the slow run from -0.10 V);
the true end is `illustrative_guarantee_refined` (a 16-level certificate). -/
theorem rise_deadline_bracket (τ : ℝ) :
    (τ < 2.168 → ¬ ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
          ∀ t ∈ Icc s e, s + τ ≤ t → 1.35 ≤ v t) ∧
    (2.26 ≤ τ → ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, u t ≤ 0.40) →
          ∀ t ∈ Icc s e, s + τ ≤ t → 1.35 ≤ v t) := by
  refine ⟨fun hτ hall => ?_, fun hτ u v a b h h0 s e hs he hu t ht htime =>
    (illustrative_guarantee_refined u v a b h h0).2.1 s e hs he hu t ht (by linarith)⟩
  obtain ⟨u, v, t, htraj, h0, hu, ht, hτt, hlt⟩ := rise_deadline_counterexample hτ
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  have hVIL : illustrative.VIL = 0.40 := by norm_num [illustrative]
  have hVOH : illustrative.VOH = 1.35 := by norm_num [illustrative]
  rw [hsafe] at h0
  rw [hVOH] at hlt
  have := hall u v 0 10 htraj h0 0 10 le_rfl le_rfl
    (fun x hx => by rw [← hVIL]; exact hu x hx) t ht hτt
  linarith

/-- **Fall bracket.** The fall claim of the guarantee with deadline `τ` (item 3
of `illustrative_guarantee`, with `τ` in place of 2.57 ns) is false for every
`τ < 1.0234` ns and true for every `τ ≥ 1.425` ns. For `1.0234 ≤ τ < 1.425`
this statement says nothing, and no other statement of the library decides the
claim.

The false end is `fall_deadline_counterexample` (the slow run from 2.08 V);
the true end is `illustrative_guarantee_refined` (a 16-level certificate). -/
theorem fall_deadline_bracket (τ : ℝ) :
    (τ < 1.0234 → ¬ ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
          ∀ t ∈ Icc s e, s + τ ≤ t → v t ≤ 0.25) ∧
    (1.425 ≤ τ → ∀ (u v : ℝ → ℝ) (a b : ℝ), IsTrajectory illustrative u v a b →
        v a ∈ Icc (-0.10 : ℝ) 2.08 →
        ∀ s e : ℝ, a ≤ s → e ≤ b → (∀ t ∈ Ico s e, 1.25 ≤ u t) →
          ∀ t ∈ Icc s e, s + τ ≤ t → v t ≤ 0.25) := by
  refine ⟨fun hτ hall => ?_, fun hτ u v a b h h0 s e hs he hu t ht htime =>
    (illustrative_guarantee_refined u v a b h h0).2.2 s e hs he hu t ht (by linarith)⟩
  obtain ⟨u, v, t, htraj, h0, hu, ht, hτt, hgt⟩ := fall_deadline_counterexample hτ
  have hsafe : illustrative.Safe = Icc (-0.10 : ℝ) 2.08 := by
    norm_num [Design.Safe, illustrative]
  have hVIH : illustrative.VIH = 1.25 := by norm_num [illustrative]
  have hVOL : illustrative.VOL = 0.25 := by norm_num [illustrative]
  rw [hsafe] at h0
  rw [hVOL] at hgt
  have := hall u v 0 10 htraj h0 0 10 le_rfl le_rfl
    (fun x hx => by rw [← hVIH]; exact hu x hx) t ht hτt
  linarith

/-- **A 1.64 ns rise deadline is false even for a start at 0.25 V**, the
highest valid-low output level: there is a trajectory of the illustrative
record with a valid-low input at all times that starts at 0.25 V and is not
valid-high at 1.64 ns. The witness is `slow_rise_run` started at 0.25 V, with
the input held at 0.40 V.

The start is fixed by the statement (`v 0 = 0.25`), so the witness is a run
that is subject to the current balance from the first instant. -/
theorem rise_deadline_1p64_is_false_from_valid_low :
    ∃ u v : ℝ → ℝ, (∀ t, u t ≤ 0.40) ∧
      IsTrajectory illustrative u v 0 10 ∧ v 0 = 0.25 ∧ v 1.64 < 1.35 := by
  have hv₀ : (0.25 : ℝ) ∈ illustrative.Safe := by norm_num [Design.Safe, illustrative]
  obtain ⟨v, hv0, -, htraj, hup⟩ := slow_rise_run 0.25 hv₀
  refine ⟨fun _ => 0.40, v, fun _ => le_rfl, htraj, hv0, ?_⟩
  have := hup 1.64 (by norm_num)
  norm_num at this ⊢
  linarith

end VoltageToBit.Examples
