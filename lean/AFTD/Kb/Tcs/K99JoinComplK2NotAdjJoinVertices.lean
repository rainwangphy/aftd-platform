import AFTD.Prelude
import AFTD.Kb.Tcs.K99JoinComplK2
import AFTD.Kb.Tcs.SimpleGraphPendantTripleExpandLeafAdj

/-!
# k99_join_compl_k2_not_adj_join_vertices

Topic: graphs   Node: c54716c061b5

Provenance: helper lemma. arXiv:2611.09347 Definition 1 -- A Structural Lower Bound for the Ramsey Number of the Petersen Graph

In the complete bipartite join graph K_{9,9} ∨ Compl(K_2), the two vertices in the independent set of size 2 are not adjacent to each other.
-/

/-- The two join vertices in K_{9,9} ∨ K_2ᶜ are not adjacent. -/
theorem k99_join_compl_k2_not_adj_join_vertices (v1 v2 : Fin 2) :
    ¬ k99_join_compl_k2.Adj (Sum.inr (Sum.inr v1)) (Sum.inr (Sum.inr v2)) := by first | exact simple_graph_pendant_triple_expand_leaf_adj | (apply simple_graph_pendant_triple_expand_leaf_adj <;> assumption) | (apply simple_graph_pendant_triple_expand_leaf_adj <;> simp_all) | simpa using simple_graph_pendant_triple_expand_leaf_adj | (simp only [k99_join_compl_k2] at *; first | exact simple_graph_pendant_triple_expand_leaf_adj | (apply simple_graph_pendant_triple_expand_leaf_adj <;> assumption) | (apply simple_graph_pendant_triple_expand_leaf_adj <;> simp_all) | simpa using simple_graph_pendant_triple_expand_leaf_adj)
