import AFTD.Prelude

/-!
# distinct_subset_sums_root_matrix

Topic: combinatorics   Node: 65b9ce33b1af

Provenance: formalization of a published result. Source: arXiv:2610.26970:429

For a natural number k, distinct_subset_sums_root_matrix k is the real k × k matrix H whose (i, j)-th entry is (if i = j then (1 : ℝ) else 0) - 1 / ((k : ℝ) + 1).
-/

/-- The root lattice matrix H = I_k - (1 / (k + 1)) 1 1ᵀ of dimension k. -/
noncomputable def distinct_subset_sums_root_matrix (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (if i = j then (1 : ℝ) else 0) - 1 / ((k : ℝ) + 1)
