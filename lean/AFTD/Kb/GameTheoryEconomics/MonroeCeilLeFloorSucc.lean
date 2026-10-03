import AFTD.Prelude

/-!
# monroe_ceil_le_floor_succ

Topic: social_choice   Node: 5396fa73af6f

⌈n/k⌉ ≤ ⌊n/k⌋ + 1, written (n + k - 1)/k ≤ n/k + 1, for all natural n, k.
-/

/-- ⌈n/k⌉ ≤ ⌊n/k⌋ + 1, written (n + k - 1)/k ≤ n/k + 1, for all natural n, k. -/
theorem monroe_ceil_le_floor_succ (n k : ℕ) : (n + k - 1) / k ≤ n / k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · calc (n + k - 1) / k ≤ (n + k) / k := Nat.div_le_div_right (by omega)
      _ = n / k + 1 := Nat.add_div_right n hk
