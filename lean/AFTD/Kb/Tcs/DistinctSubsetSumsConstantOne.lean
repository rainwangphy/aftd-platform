import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctSubsetSumsConstant

/-!
# distinct_subset_sums_constant_one

Topic: combinatorics   Node: 494648ece5ea

Provenance: formalization of a published result. Source: arXiv:2610.26970 line 166

The constant distinct_subset_sums_constant at k = 1 equals Real.sqrt (2 / Real.pi).
-/

/-- In dimension 1, the distinct subset sum constant C_1 equals sqrt(2/pi). -/
theorem distinct_subset_sums_constant_one :
    distinct_subset_sums_constant 1 = Real.sqrt (2 / Real.pi) := by
  unfold distinct_subset_sums_constant
  norm_num
