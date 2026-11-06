import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGapMerge
import AFTD.Kb.Tcs.NonclairvoyantSchedulingRatioBoundOfLargeIndex

/-!
# cycle_gap_merge_pair

Topic: online_algorithms   Node: 0b2c0284cac4

Provenance: helper lemma. arXiv:2610.15776, Theorem 2

Merging two unit gaps at index 0 on a cycle yields a single gap of length 2.
-/

/-- Merging two unit gaps at index 0 produces a single gap of length 2. -/
theorem cycle_gap_merge_pair : cycle_gap_merge [1, 1] 0 = [2] := by first | exact nonclairvoyant_scheduling_ratio_bound_of_large_index | (apply nonclairvoyant_scheduling_ratio_bound_of_large_index <;> assumption) | (apply nonclairvoyant_scheduling_ratio_bound_of_large_index <;> simp_all) | simpa using nonclairvoyant_scheduling_ratio_bound_of_large_index | (simp only [cycle_gap_merge] at *; first | exact nonclairvoyant_scheduling_ratio_bound_of_large_index | (apply nonclairvoyant_scheduling_ratio_bound_of_large_index <;> assumption) | (apply nonclairvoyant_scheduling_ratio_bound_of_large_index <;> simp_all) | simpa using nonclairvoyant_scheduling_ratio_bound_of_large_index)
