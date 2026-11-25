import AFTD.Prelude

/-!
# consecutive_sum_bound_k

Topic: combinatorics   Node: c1e4c0f3fba9

Provenance: formalization of a published result. Source: arXiv:2611.30462 Theorem 3.2

For integers a and K, the index k = ⌊2√(a/K - 1)⌋ as a natural number.
-/

/-- The parameter k = ⌊2√(a/K - 1)⌋ for the lower bound on sequences with distinct consecutive sums. -/
noncomputable def consecutive_sum_bound_k (a K : ℤ) : ℕ := Nat.floor (2 * Real.sqrt ((a : ℝ) / (K : ℝ) - 1))
