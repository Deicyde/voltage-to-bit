import Mathlib.Analysis.Calculus.MeanValue

/-!
# Positive-part square

`psq x = (max x 0)²` is the building block of the square-law device model.
This file collects the order and Lipschitz facts used later. No circuit content.
-/

namespace VoltageToBit

/-- Positive-part square: `psq x = (max x 0)²`. -/
noncomputable def psq (x : ℝ) : ℝ := (max x 0) ^ 2

theorem psq_nonneg (x : ℝ) : 0 ≤ psq x := sq_nonneg _

theorem psq_of_nonneg {x : ℝ} (h : 0 ≤ x) : psq x = x ^ 2 := by
  simp [psq, max_eq_left h]

theorem psq_of_nonpos {x : ℝ} (h : x ≤ 0) : psq x = 0 := by
  simp [psq, max_eq_right h]

/-- Case form, convenient for evaluating `psq` on numerals. -/
theorem psq_eq_ite (x : ℝ) : psq x = if 0 ≤ x then x ^ 2 else 0 := by
  split_ifs with h
  · exact psq_of_nonneg h
  · exact psq_of_nonpos (le_of_not_ge h)

theorem psq_mono {x y : ℝ} (h : x ≤ y) : psq x ≤ psq y := by
  unfold psq
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 h) 2

/-- Increments of `psq` over a fixed nonnegative step are monotone in the base
point (convexity of `psq`). -/
theorem psq_incr_mono {d x y : ℝ} (hd : 0 ≤ d) (h : x ≤ y) :
    psq (x + d) - psq x ≤ psq (y + d) - psq y := by
  rcases le_total 0 x with hx | hx
  · rw [psq_of_nonneg (by linarith : (0 : ℝ) ≤ x + d), psq_of_nonneg hx,
      psq_of_nonneg (by linarith : (0 : ℝ) ≤ y + d), psq_of_nonneg (by linarith : (0 : ℝ) ≤ y)]
    nlinarith
  · rcases le_total 0 y with hy | hy
    · rcases le_total 0 (x + d) with hxd | hxd
      · rw [psq_of_nonneg hxd, psq_of_nonpos hx,
          psq_of_nonneg (by linarith : (0 : ℝ) ≤ y + d), psq_of_nonneg hy]
        nlinarith
      · rw [psq_of_nonpos hxd, psq_of_nonpos hx,
          psq_of_nonneg (by linarith : (0 : ℝ) ≤ y + d), psq_of_nonneg hy]
        nlinarith
    · rw [psq_of_nonpos hx, psq_of_nonpos hy]
      have := psq_mono (by linarith : x + d ≤ y + d)
      linarith

/-- The comparison used for every current margin: a difference `psq p - psq q`
with `q ≤ p` does not decrease when the lower argument moves up and the gap
does not shrink. -/
theorem psq_sub_le_psq_sub {p q p' q' : ℝ} (hqp : q ≤ p) (hq : q ≤ q')
    (hd : p - q ≤ p' - q') : psq p - psq q ≤ psq p' - psq q' := by
  have h1 := psq_incr_mono (d := p - q) (x := q) (y := q') (by linarith) hq
  have h2 : psq (q' + (p - q)) ≤ psq p' := psq_mono (by linarith)
  have h3 : q + (p - q) = p := by ring
  rw [h3] at h1
  linarith

/-- `psq` is locally Lipschitz with an explicit modulus. -/
theorem abs_psq_sub_le (x y : ℝ) : |psq x - psq y| ≤ (|x| + |y|) * |x - y| := by
  have h1 : |max x 0 - max y 0| ≤ |x - y| := abs_max_sub_max_le_abs x y 0
  have hx0 : 0 ≤ max x 0 := le_max_right _ _
  have hy0 : 0 ≤ max y 0 := le_max_right _ _
  have hx : max x 0 ≤ |x| := max_le (le_abs_self x) (abs_nonneg x)
  have hy : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have hfac : psq x - psq y = (max x 0 - max y 0) * (max x 0 + max y 0) := by
    unfold psq; ring
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ max x 0 + max y 0), mul_comm]
  exact mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity)

theorem continuous_psq : Continuous psq := by
  unfold psq
  fun_prop

end VoltageToBit
