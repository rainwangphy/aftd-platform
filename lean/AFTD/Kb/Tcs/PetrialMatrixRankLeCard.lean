import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_matrix_rank_le_card

Topic: combinatorics   Node: c64a6396abaf

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

For any finite simple graph G and any subset F of vertices, the rank of the petrial matrix of G and F over ZMod 2 is at most the number of vertices.
-/

/-- For any finite simple graph G and subset F, the rank of petrial_matrix G F is at most |V|. -/
theorem petrial_matrix_rank_le_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset V) :
    (petrial_matrix G F).rank ≤ Fintype.card V := Matrix.rank_le_card_width _
