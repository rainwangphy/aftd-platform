import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0LtOne

/-!
# magic_square_upper_slope_constant_eq

Topic: quantum   Node: 5479de80ce6f

Provenance: formalization of a published result. Source: arXiv:2610.12001 Cor. 6.2

The upper bound slope constant $3 / (4(1 - \beta_0))$ for the magic square predictability loss equals $27(1 + \sqrt{2/3}) / 4$, where $\beta_0 = \mathrm{magic\_square\_threshold\_beta0}$.
-/

/-- The upper slope bound constant 3 / (4 * (1 - beta_0)) in Corollary 6.2 of arXiv:2610.12001 equals 27 * (1 + sqrt(2/3)) / 4. -/
theorem magic_square_upper_slope_constant_eq :
    3 / (4 * (1 - magic_square_threshold_beta0)) = 27 * (1 + Real.sqrt (2 / 3)) / 4 := by
  have h_lt : magic_square_threshold_beta0 < 1 := magic_square_threshold_beta0_lt_one
  have h_denom : 4 * (1 - magic_square_threshold_beta0) ≠ 0 := by linarith
  rw [div_eq_div_iff h_denom (by norm_num)]
  have hs : (Real.sqrt (2 / 3)) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hβ : magic_square_threshold_beta0 = (2 + Real.sqrt (2 / 3)) / 3 := rfl
  rw [hβ]
  generalize Real.sqrt (2 / 3) = s at hs ⊢
  linear_combination 36 * hs
