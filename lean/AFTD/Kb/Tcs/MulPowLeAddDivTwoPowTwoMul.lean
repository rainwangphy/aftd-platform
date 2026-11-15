import AFTD.Prelude

/-!
# mul_pow_le_add_div_two_pow_two_mul

Topic: combinatorics   Node: 565160c63257

Provenance: helper lemma. arXiv:2611.15027 Section 6.1

For any nonnegative real numbers u and v and any natural number k, (u * v)^k is at most ((u + v) / 2)^(2 * k).
-/

/-- The AM-GM inequality for power products: (u * v)^k ≤ ((u + v) / 2)^(2 * k) for nonnegative reals. -/
lemma mul_pow_le_add_div_two_pow_two_mul (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (k : ℕ) :
    (u * v) ^ k ≤ ((u + v) / 2) ^ (2 * k) := by
  have h : u * v ≤ ((u + v) / 2) ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have h0 : 0 ≤ u * v := mul_nonneg hu hv
  calc (u * v) ^ k ≤ (((u + v) / 2) ^ 2) ^ k := pow_le_pow_left₀ h0 h k
    _ = ((u + v) / 2) ^ (2 * k) := by rw [pow_mul]
