import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLabelingComplete

/-!
# cycle_labeling_complete_nine

Topic: combinatorics   Node: bb51d5be6aac

Provenance: original. Related work: arXiv:2610.08889 (Consecutive Cycle Sums), list entry OP-121: a complete placement for n = 9 (the increasing order is incomplete by Theorem 1).

The 9-cycle labelled 1, 2, 3, 4, 5, 6, 8, 9, 7 in order is complete.
-/

theorem cycle_labeling_complete_nine : cycle_labeling_complete 9 [1, 2, 3, 4, 5, 6, 8, 9, 7] := by
  unfold cycle_labeling_complete; decide
