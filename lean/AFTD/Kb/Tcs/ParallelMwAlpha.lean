import AFTD.Prelude

/-!
# parallel_mw_alpha

Topic: combinatorics   Node: 949f5d0091bb

Provenance: formalization of a published result. Source: arXiv:2610.27706, Eq. (10)

For natural numbers n and r, parallel_mw_alpha n r is the real number defined by 2 * ∑ j ∈ Finset.range r, ((n - 1).choose j : ℝ).
-/

/-- The Tutte evaluation alpha = T(2,0) defined as a real-valued sum of binomial coefficients. -/
def parallel_mw_alpha (n r : ℕ) : ℝ := 2 * ∑ j ∈ Finset.range r, ((n - 1).choose j : ℝ)
