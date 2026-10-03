import AFTD.Prelude

/-!
# ef1cost_alpha_pos

Topic: fair_division   Node: c66333d88942

3 - 2 sqrt 2 is positive.
-/

lemma ef1cost_alpha_pos : 0 < 3 - 2 * Real.sqrt 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  nlinarith
