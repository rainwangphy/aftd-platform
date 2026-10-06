import AFTD.Prelude

/-!
# monroe_ceil_le_floor_succ

Topic: social_choice   Node: 5396fa73af6f

Provenance: helper lemma. step towards hare_monroe_satisfies_droop_jr (Monroe and Droop-JR, open case of Justified Representation: From Hare to Droop, arXiv:2508.00811)

⌈n/k⌉ ≤ ⌊n/k⌋ + 1, written (n + k - 1)/k ≤ n/k + 1, for all natural n, k.
-/

/-- ⌈n/k⌉ ≤ ⌊n/k⌋ + 1, written (n + k - 1)/k ≤ n/k + 1, for all natural n, k. -/
theorem monroe_ceil_le_floor_succ (n k : ℕ) : (n + k - 1) / k ≤ n / k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · calc (n + k - 1) / k ≤ (n + k) / k := Nat.div_le_div_right (by omega)
      _ = n / k + 1 := Nat.add_div_right n hk
