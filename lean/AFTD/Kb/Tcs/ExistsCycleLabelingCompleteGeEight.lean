import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLabelingComplete

/-!
# exists_cycle_labeling_complete_ge_eight

Topic: combinatorics   Node: 28f30366582d

Provenance: original. Related work: arXiv:2610.08889 (Consecutive Cycle Sums), question after Theorem 1 (list entry OP-121): Theorem 1 shows the increasing order is incomplete for n ≥ 8; the paper does not consider other orders. Answered here by the explicit witness 1, 2, 3, 4, 5, 6, 8, 7 for n = 8.

There is an n ≥ 8 and a placement of 1, …, n around the n-cycle that is complete: for n = 8, the order 1, 2, 3, 4, 5, 6, 8, 7.
-/

theorem exists_cycle_labeling_complete_ge_eight :
    ∃ n ≥ 8, ∃ L : List ℕ, cycle_labeling_complete n L :=
  ⟨8, le_rfl, [1, 2, 3, 4, 5, 6, 8, 7], by unfold cycle_labeling_complete; decide⟩
