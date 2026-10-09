import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLabelingComplete

/-!
# cycle_labeling_complete_ten

Topic: combinatorics   Node: 5ec2f15835f5

Provenance: original. Related work: arXiv:2610.08889 (Consecutive Cycle Sums), list entry OP-121: a complete placement for n = 10 (found by computer search).

The 10-cycle labelled 1, 2, 3, 4, 5, 9, 7, 8, 6, 10 in order is complete.
-/

theorem cycle_labeling_complete_ten : cycle_labeling_complete 10 [1, 2, 3, 4, 5, 9, 7, 8, 6, 10] := by
  unfold cycle_labeling_complete; decide
