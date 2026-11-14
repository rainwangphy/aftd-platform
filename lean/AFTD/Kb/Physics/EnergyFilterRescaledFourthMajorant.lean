import AFTD.Prelude

/-!
# energy_filter_rescaled_fourth_majorant

Topic: statistical_mechanics   Node: d56d0b7bb4f5

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For nonnegative b, if b≤exp(−y²/2) and |x−y|≤1, then b⁴≤exp(2)exp(−x²).
-/

theorem energy_filter_rescaled_fourth_majorant (b x y : ℝ)
    (hb0 : 0 ≤ b) (hb : b ≤ Real.exp (-(y^2/2))) (hxy : |x-y| ≤ 1) :
    b^4 ≤ Real.exp 2 * Real.exp (-x^2) := by
  have hdist := abs_le.mp hxy
  have hsq : (x-y)^2 ≤ 1 := by nlinarith
  have hquad : -2*y^2 ≤ 2-x^2 := by nlinarith [sq_nonneg (x-2*y)]
  calc
    b^4 ≤ (Real.exp (-(y^2/2)))^4 := pow_le_pow_left₀ hb0 hb 4
    _ = Real.exp (-2*y^2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    _ ≤ Real.exp (2-x^2) := Real.exp_le_exp.mpr hquad
    _ = Real.exp 2 * Real.exp (-x^2) := by rw [← Real.exp_add]; congr 1
