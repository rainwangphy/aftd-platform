import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialMatrixRankLeCard
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_coeff_eq_zero_of_gt_card

Topic: combinatorics   Node: e90e0a09ff51

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

For any finite simple graph G and any integer k strictly greater than the number of vertices, petrial_coeff G k equals 0.
-/

/-- The partial Petrial coefficient vanishes for indices strictly exceeding |V|. -/
theorem petrial_coeff_eq_zero_of_gt_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : Fintype.card V < k) :
    petrial_coeff G k = 0 := by
  unfold petrial_coeff
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  have h_le := petrial_matrix_rank_le_card G x
  omega
