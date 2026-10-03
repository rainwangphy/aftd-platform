import AFTD.Prelude

/-!
# cube_tangent_le

Topic: mechanism_design   Node: 13ca71d2f091

For a, b >= 0, the tangent of t^3 at b lies below the cube at a: b^3 + 3 b^2 (a - b) <= a^3.
-/

lemma cube_tangent_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : b ^ 3 + 3 * b ^ 2 * (a - b) ≤ a ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (by linarith : 0 ≤ a + 2 * b)]
