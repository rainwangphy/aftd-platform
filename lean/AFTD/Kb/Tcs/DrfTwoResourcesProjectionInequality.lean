import AFTD.Prelude

/-!
# drf_two_resources_projection_inequality

Topic: online_algorithms   Node: 46454351ecc0

Provenance: formalization of a published result. Source: arXiv:2611.07905 Lemma 14

For all real numbers x, y in [0, 1] with x + y >= 1, max(x, y) <= ((1 + Real.sqrt 3) / 4) * (x^2 + (1 - x)^2 + (1 - y)^2 + y^2).
-/

/-- Geometric inequality bounding congestion by projected resource loads for two resources (Lemma 14). -/
theorem drf_two_resources_projection_inequality (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hsum : 1 ≤ x + y) : max x y ≤ (1 + Real.sqrt 3) / 4 * (x ^ 2 + (1 - x) ^ 2 + (1 - y) ^ 2 + y ^ 2) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hx : x ≤ (1 + Real.sqrt 3) / 4 * (x ^ 2 + (1 - x) ^ 2 + (1 - y) ^ 2 + y ^ 2) := by
    have h_id : (1 + Real.sqrt 3) / 4 * (x ^ 2 + (1 - x) ^ 2 + (1 - y) ^ 2 + y ^ 2) - x =
        (1 + Real.sqrt 3) / 2 * ((x - Real.sqrt 3 / 2) ^ 2 + (y - 1 / 2) ^ 2) := by
      linear_combination (x / 2 - (1 + Real.sqrt 3) / 8) * hs
    have h_pos : 0 ≤ (1 + Real.sqrt 3) / 2 * ((x - Real.sqrt 3 / 2) ^ 2 + (y - 1 / 2) ^ 2) := by
      positivity
    linarith
  have hy : y ≤ (1 + Real.sqrt 3) / 4 * (x ^ 2 + (1 - x) ^ 2 + (1 - y) ^ 2 + y ^ 2) := by
    have h_id : (1 + Real.sqrt 3) / 4 * (x ^ 2 + (1 - x) ^ 2 + (1 - y) ^ 2 + y ^ 2) - y =
        (1 + Real.sqrt 3) / 2 * ((x - 1 / 2) ^ 2 + (y - Real.sqrt 3 / 2) ^ 2) := by
      linear_combination (y / 2 - (1 + Real.sqrt 3) / 8) * hs
    have h_pos : 0 ≤ (1 + Real.sqrt 3) / 2 * ((x - 1 / 2) ^ 2 + (y - Real.sqrt 3 / 2) ^ 2) := by
      positivity
    linarith
  exact max_le hx hy
