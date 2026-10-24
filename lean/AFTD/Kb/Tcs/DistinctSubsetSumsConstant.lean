import AFTD.Prelude

/-!
# distinct_subset_sums_constant

Topic: combinatorics   Node: fe5f7b7414e8

Provenance: formalization of a published result. Source: arXiv:2610.26970 Thm 1.2

For a natural number k : ℕ, distinct_subset_sums_constant k is defined as Real.sqrt (2 * (k : ℝ) / Real.pi) * ((k : ℝ) + 1) ^ (((k : ℝ) - 1) / (2 * (k : ℝ))) / Real.sqrt (Nat.floor (((k : ℝ) + 1) ^ 2 / 4)).
-/

/-- The asymptotic leading constant C_k for k-dimensional distinct subset sum lower bounds. -/
noncomputable def distinct_subset_sums_constant (k : ℕ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) / Real.pi) *
    ((k : ℝ) + 1) ^ (((k : ℝ) - 1) / (2 * (k : ℝ))) /
    Real.sqrt (Nat.floor (((k : ℝ) + 1) ^ 2 / 4))
