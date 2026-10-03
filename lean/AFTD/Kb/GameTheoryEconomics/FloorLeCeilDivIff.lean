import AFTD.Prelude

/-!
# floor_le_ceil_div_iff

Topic: social_choice   Node: 4fbaed30c24c

For S > 0, floor(x/S) <= a <= ceil(x/S) iff x < (a+1) S and a S < x + S.
-/

/-- Natural-number form of one state's quota condition: with total population `S > 0`, `⌊x/S⌋ ≤ a ≤ ⌈x/S⌉` iff `x < (a+1) S` and `a S < x + S`. -/
lemma floor_le_ceil_div_iff (x S a : ℕ) (hS : 0 < S) :
    (⌊(x : ℚ) / (S : ℚ)⌋₊ ≤ a ∧ a ≤ ⌈(x : ℚ) / (S : ℚ)⌉₊) ↔ (x < (a + 1) * S ∧ a * S < x + S) := by
  have hS' : (0 : ℚ) < S := by exact_mod_cast hS
  have hy : (0 : ℚ) ≤ (x : ℚ) / S := div_nonneg (Nat.cast_nonneg x) hS'.le
  have h1 : ⌊(x : ℚ) / (S : ℚ)⌋₊ ≤ a ↔ x < (a + 1) * S := by
    rw [← Nat.lt_succ_iff, Nat.floor_lt hy, div_lt_iff₀ hS']
    norm_cast
  have h2 : a ≤ ⌈(x : ℚ) / (S : ℚ)⌉₊ ↔ a * S < x + S := by
    cases a with
    | zero => simp; omega
    | succ b =>
      rw [Nat.succ_le_iff, Nat.lt_ceil, lt_div_iff₀ hS']
      constructor
      · intro h; have : b * S < x := by exact_mod_cast h
        rw [Nat.succ_mul]; omega
      · intro h; rw [Nat.succ_mul] at h
        exact_mod_cast (show b * S < x by omega)
  rw [h1, h2]
