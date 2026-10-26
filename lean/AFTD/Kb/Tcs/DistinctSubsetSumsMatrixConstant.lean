import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctSubsetSumsQuadMax

/-!
# distinct_subset_sums_matrix_constant

Topic: combinatorics   Node: a34e92bf864e

Provenance: formalization of a published result. Source: arXiv:2610.26970 Proposition 3.1

For a natural number k and a real k × k matrix A, distinct_subset_sums_matrix_constant k A is defined as Real.sqrt (2 * (k : ℝ) / Real.pi) * (Matrix.det A ^ (1 / (2 * (k : ℝ)))) / Real.sqrt (distinct_subset_sums_quad_max k A).
-/

/-- The Gaussian subset sum constant C(A) associated with a k × k matrix A. -/
noncomputable def distinct_subset_sums_matrix_constant (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) / Real.pi) * (Matrix.det A ^ (1 / (2 * (k : ℝ)))) /
    Real.sqrt (distinct_subset_sums_quad_max k A)
