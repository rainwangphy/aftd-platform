import AFTD.Prelude

/-!
# ef1cost_alpha_lt_half

Topic: fair_division   Node: 1acb163602e1

3 - 2 sqrt 2 is less than 1/2.
-/

lemma ef1cost_alpha_lt_half : 3 - 2 * Real.sqrt 2 < 1 / 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  nlinarith
