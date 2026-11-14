import AFTD.Prelude

/-!
# star_core_exponent

Topic: quantum   Node: 7fbfc02fdea9

Provenance: formalization of a published result. Source: arXiv:2610.26814, Theorem 3.1 and Eq. (46)

For a star-core graph with k vertices, center block size b, and leaf block sizes a_1, ..., a_{k-1} summing to Q = b + sum_i a_i, the assignment sum exponent X_n(b, a) at replica order n is defined by sum_i n^(Q - a_i) + prod_i (n^(a_i) - n + 1).
-/

/-- The assignment sum exponent X_n for a star-core graph with center b and leaves a_1, ..., a_{k-1}. -/
def star_core_exponent (k : ℕ) (n : ℕ) (b : ℕ) (a : Fin (k - 1) → ℕ) : ℕ :=
  let Q := b + ∑ i, a i
  (∑ i, n ^ (Q - a i)) + ∏ i, (n ^ a i - n + 1)
