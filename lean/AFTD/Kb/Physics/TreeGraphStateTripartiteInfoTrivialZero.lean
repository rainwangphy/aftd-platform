import AFTD.Prelude
import AFTD.Kb.Physics.SimpleGraphCutRank
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfo

/-!
# tree_graph_state_tripartite_info_trivial_zero

Topic: quantum_mechanics   Node: 9d4eec658f0c

Provenance: helper lemma. arXiv:2511.19585

For any finite graph G on type V with decidable equality and decidable adjacency, tree_graph_state_tripartite_info G Finset.univ ∅ ∅ ∅ equals 0.
-/

lemma tree_graph_state_tripartite_info_trivial_zero_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    simple_graph_cut_rank G ∅ = 0 := by
  dsimp [simple_graph_cut_rank]
  have h := Matrix.rank_le_card_height ((G.adjMatrix (ZMod 2)).submatrix (Subtype.val : ↥(∅ : Finset V) → V) (Subtype.val : ↥((∅ : Finset V)ᶜ) → V))
  simp only [Fintype.card_coe, Finset.card_empty] at h
  omega

lemma tree_graph_state_tripartite_info_trivial_zero_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    simple_graph_cut_rank G Finset.univ = 0 := by
  dsimp [simple_graph_cut_rank]
  have h := Matrix.rank_le_card_width ((G.adjMatrix (ZMod 2)).submatrix (Subtype.val : ↥(Finset.univ : Finset V) → V) (Subtype.val : ↥((Finset.univ : Finset V)ᶜ) → V))
  simp only [Finset.compl_univ, Fintype.card_coe, Finset.card_empty] at h
  omega

/-- The trivial four-partition (V, ∅, ∅, ∅) of any finite graph has tripartite information zero. -/
theorem tree_graph_state_tripartite_info_trivial_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    tree_graph_state_tripartite_info G Finset.univ ∅ ∅ ∅ = 0 := by
  dsimp [tree_graph_state_tripartite_info]
  simp only [Finset.union_empty]
  rw [tree_graph_state_tripartite_info_trivial_zero_univ,
      tree_graph_state_tripartite_info_trivial_zero_empty]
  ring
