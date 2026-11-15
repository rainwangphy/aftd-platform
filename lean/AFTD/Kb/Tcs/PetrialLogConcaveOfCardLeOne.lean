import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.PetrialCoeffEqZeroOfGtCard
import AFTD.Kb.Tcs.PetrialCoeff

/-!
# petrial_log_concave_of_card_le_one

Topic: combinatorics   Node: 0c4e3d76bbcb

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

Every simple graph on at most 1 vertex satisfies petrial_log_concave G.
-/

/-- Any simple graph on at most one vertex has log-concave partial Petrial polynomial. -/
theorem petrial_log_concave_of_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 1) :
    petrial_log_concave G := by
  intro k ⟨i, hi, hni⟩ ⟨j, hj, hnj⟩
  have hj_gt : Fintype.card V < j := by omega
  have hj_zero := petrial_coeff_eq_zero_of_gt_card G hj_gt
  exact (hnj hj_zero).elim
