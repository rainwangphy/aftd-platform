import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLabelingComplete

/-!
# not_cycle_labeling_complete_range_eight

Topic: combinatorics   Node: a3229c23c911

Provenance: formalization of a published result. Source: arXiv:2610.08889 (Consecutive Cycle Sums), Theorem 1, case n = 8 (Sec. 5 notes 17 and 19 are missing).

The 8-cycle labelled 1, …, 8 in order is not complete (17 and 19 are not arc sums).
-/

theorem not_cycle_labeling_complete_range_eight :
    ¬ cycle_labeling_complete 8 (List.range' 1 8) := by
  unfold cycle_labeling_complete; decide
