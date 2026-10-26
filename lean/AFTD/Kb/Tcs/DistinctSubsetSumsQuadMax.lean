import AFTD.Prelude

/-!
# distinct_subset_sums_quad_max

Topic: combinatorics   Node: 282aa3748c68

Provenance: formalization of a published result. Source: arXiv:2610.26970 Proposition 3.1

For a natural number k and a real k × k matrix A, distinct_subset_sums_quad_max k A is the supremum over all vectors u in the unit cube Set.Icc (0 : Fin k → ℝ) 1 of the quadratic form dotProduct u (Matrix.mulVec A u).
-/

/-- The maximum value b_A of the quadratic form uᵀ A u over the unit cube [0, 1]^k. -/
noncomputable def distinct_subset_sums_quad_max (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  sSup { dotProduct u (Matrix.mulVec A u) | (u : Fin k → ℝ) (_ : u ∈ Set.Icc 0 1) }
