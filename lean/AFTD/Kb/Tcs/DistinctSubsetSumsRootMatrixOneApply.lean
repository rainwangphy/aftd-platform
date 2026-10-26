import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctSubsetSumsRootMatrix

/-!
# distinct_subset_sums_root_matrix_one_apply

Topic: combinatorics   Node: d3c049172523

Provenance: helper lemma. arXiv:2610.26970:429

The entry at index (0, 0) of distinct_subset_sums_root_matrix 1 equals 1 / 2.
-/

/-- The single entry of the 1 × 1 root lattice matrix is 1/2. -/
theorem distinct_subset_sums_root_matrix_one_apply :
  distinct_subset_sums_root_matrix 1 0 0 = 1 / 2 := by
  simp [distinct_subset_sums_root_matrix]
  norm_num
