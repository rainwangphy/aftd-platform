import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0

/-!
# magic_square_threshold_beta0_lt_one

Topic: quantum   Node: 8d186d838765

Provenance: helper lemma. arXiv:2610.12001, Section 6 and Corollary 6.2; analysis of the right-hand secant limit.

The magic-square threshold is strictly below one.
-/

theorem magic_square_threshold_beta0_lt_one : magic_square_threshold_beta0 < 1 := by
  have hs : Real.sqrt (2 / 3) = Real.sqrt 6 / 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    linear_combination (-1 / 9 : ℝ) * this
  have h6 : Real.sqrt 6 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [magic_square_threshold_beta0, hs]
  linarith
