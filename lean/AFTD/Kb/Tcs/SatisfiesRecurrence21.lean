import AFTD.Prelude

/-!
# satisfies_recurrence_2_1

Topic: combinatorics   Node: adc6cdbfc2c3

Provenance: formalization of a published result. Source: arXiv:2611.01561, equation (2.1)

Real coefficients a, b, c : Fin (N + 1) → ℝ satisfy condition (2.1) if a 0 = 1, b 0 = 0, c 0 = 0, a N = 0, a i + b i + c i = 1 for all i, a i > 0 for all i with i.val < N, and c i > 0 for all i with 0 < i.val.
-/

/-- Condition (2.1) of arXiv:2611.01561 for normalized finite orthogonal polynomial recurrences. -/
def satisfies_recurrence_2_1 (N : ℕ) (a b c : Fin (N + 1) → ℝ) : Prop := a ⟨0, Nat.zero_lt_succ N⟩ = 1 ∧
  b ⟨0, Nat.zero_lt_succ N⟩ = 0 ∧
  c ⟨0, Nat.zero_lt_succ N⟩ = 0 ∧
  a ⟨N, Nat.lt_succ_self N⟩ = 0 ∧
  (∀ i : Fin (N + 1), a i + b i + c i = 1) ∧
  (∀ i : Fin (N + 1), i.val < N → 0 < a i) ∧
  (∀ i : Fin (N + 1), 0 < i.val → 0 < c i)
