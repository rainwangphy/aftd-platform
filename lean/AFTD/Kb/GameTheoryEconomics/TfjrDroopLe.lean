import AFTD.Prelude

/-!
# tfjr_droop_le

Topic: social_choice   Node: a9d7650f5195

⌈(t+1)s/n⌉ - 1 ≤ t whenever s ≤ n.
-/

/-- ⌈(t+1)s/n⌉ - 1 ≤ t whenever s ≤ n. -/
theorem tfjr_droop_le (t s n : ℕ) (hs : s ≤ n) : ((t + 1) * s + n - 1) / n - 1 ≤ t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (t + 1) * s ≤ (t + 1) * n := Nat.mul_le_mul_left _ hs
    have h2 : (t + 2) * n = (t + 1) * n + n := by ring
    have : ((t + 1) * s + n - 1) / n < t + 2 := (Nat.div_lt_iff_lt_mul hn).2 (by omega)
    omega
