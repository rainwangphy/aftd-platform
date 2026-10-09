import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLabelingComplete

/-!
# cycle_labeling_complete_range_five

Topic: combinatorics   Node: e071160be255

Provenance: formalization of a published result. Source: arXiv:2610.08889 (Consecutive Cycle Sums), Sec. 1 (the 5-cycle is complete).

The 5-cycle labelled 1, 2, 3, 4, 5 in order is complete.
-/

theorem cycle_labeling_complete_range_five : cycle_labeling_complete 5 (List.range' 1 5) := by
  unfold cycle_labeling_complete; decide
