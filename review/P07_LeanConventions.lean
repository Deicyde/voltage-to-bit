import VoltageToBit

/-!
# Probe P07 (workstream E): Lean conventions that a consumer of the numbers must know

The theorems of the library always carry `Admissible`, so none of the facts
below makes a theorem false. They matter for anyone who *evaluates* the
definitions (an experiment harness, a search loop ranking candidate records by
`tauUp`) without first establishing admissibility.

* `noisy_tauUp_negative`: for the rejected record `noisy` the "deadline"
  `tauUp` is a negative number.
* `zeroMargin_tauUp`: for a record whose pull-up margin equals `eps` exactly,
  `tauUp = 0` because Lean defines `x / 0 = 0`. A ranking by smallest `tauUp`
  would prefer both to the admissible record.
* `decode_inverted_never_undefined`: with inverted thresholds the three-valued
  decoder has no undefined band at all (and `false` wins on the overlap). The
  band exists only because `Admissible` gives `VOL < VOH` and `VIL < VIH`.
* `nominal_not_centre`: the docstring of `nominal` says "the centre of the box";
  the threshold entries are `0.5`, the centre is `0.525`. (Cosmetic.)
-/

open VoltageToBit VoltageToBit.Examples

namespace Review.P07

theorem noisy_tauUp_negative : noisy.tauUp < 0 := by
  norm_num [noisy, illustrative, Design.tauUp, Design.Iup, psq_eq_ite]

/-- The illustrative record with `eps` equal to the pull-up margin `Iup VOH`. -/
noncomputable def zeroMargin : Design := { illustrative with eps := 10.476 }

theorem zeroMargin_not_admissible : ¬ zeroMargin.Admissible := fun h => by
  have h1 := h.up
  norm_num [zeroMargin, illustrative, Design.Iup, psq_eq_ite] at h1

theorem zeroMargin_tauUp : zeroMargin.tauUp = 0 := by
  norm_num [zeroMargin, illustrative, Design.tauUp, Design.Iup, psq_eq_ite]

theorem illustrative_tauUp_pos : 0 < illustrative.tauUp :=
  illustrative_admissible.tauUp_pos

theorem decode_inverted_never_undefined (x : ℝ) : decode 1 0 x ≠ none := by
  rw [Ne, decode_eq_none_iff]
  intro h
  linarith [h.1, h.2]

theorem decode_inverted_false_wins : decode 1 0 (1 / 2) = some false := by
  rw [decode_eq_false_iff]; norm_num

theorem nominal_not_centre :
    nominal.Vtn ≠ (illustrative.Vtnlo + illustrative.Vtnhi) / 2 ∧
    nominal.Vtp ≠ (illustrative.Vtplo + illustrative.Vtphi) / 2 := by
  constructor <;> norm_num [nominal, illustrative]

end Review.P07

#print axioms Review.P07.noisy_tauUp_negative
#print axioms Review.P07.zeroMargin_tauUp
#print axioms Review.P07.decode_inverted_never_undefined
#print axioms Review.P07.nominal_not_centre
