import AFTD.Prelude

/-!
# is_normalized_recurrence

Topic: combinatorics   Node: 56551bbae2fc

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 2, Eq. (2.1)

For N : ℕ and a, b, c : Fin (N + 1) → ℝ, the recurrence is normalized if a 0 = 1, b 0 = 0, c 0 = 0, a N = 0, a i + b i + c i = 1 for all i : Fin (N + 1), a i > 0 for all i with i.val < N, c i > 0 for all i with 0 < i.val, and b i ≥ 0 for all i : Fin (N + 1).
-/

/-- Normalized recurrence coefficients on Fin (N + 1) with row sums one. -/
def is_normalized_recurrence (N : ℕ) (a b c : Fin (N + 1) → ℝ) : Prop := a ⟨0, Nat.zero_lt_succ N⟩ = 1 ∧
  b ⟨0, Nat.zero_lt_succ N⟩ = 0 ∧
  c ⟨0, Nat.zero_lt_succ N⟩ = 0 ∧
  a ⟨N, Nat.lt_succ_self N⟩ = 0 ∧
  (∀ i : Fin (N + 1), a i + b i + c i = 1) ∧
  (∀ i : Fin (N + 1), i.val < N → 0 < a i) ∧
  (∀ i : Fin (N + 1), 0 < i.val → 0 < c i) ∧
  (∀ i : Fin (N + 1), 0 ≤ b i)
