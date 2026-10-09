import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLabelingComplete

/-!
# not_cycle_labeling_complete_range_six

Topic: combinatorics   Node: 11d524bb8670

Provenance: formalization of a published result. Source: arXiv:2610.08889 (Consecutive Cycle Sums), Sec. 1 (the 6-cycle is incomplete).

The 6-cycle labelled 1, …, 6 in order is not complete (8 and 13 are not arc sums).
-/

theorem not_cycle_labeling_complete_range_six :
    ¬ cycle_labeling_complete 6 (List.range' 1 6) := by
  unfold cycle_labeling_complete; decide
