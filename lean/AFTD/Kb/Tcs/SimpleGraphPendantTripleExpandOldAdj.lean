import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPendantTripleExpand

/-!
# simple_graph_pendant_triple_expand_old_adj

Topic: graphs   Node: aae36d22eff3

Provenance: helper lemma. Sanity lemma for simple_graph_pendant_triple_expand, the local reduction construction for OP-309.

Adjacency between original vertices after triple expansion is original adjacency with uv removed.
-/

theorem simple_graph_pendant_triple_expand_old_adj {V : Type*}
    (G : SimpleGraph V) (u v a b : V) :
    (simple_graph_pendant_triple_expand G u v).Adj (Sum.inl a) (Sum.inl b) ↔
      G.Adj a b ∧ s(a,b) ≠ s(u,v) := by
  simp [simple_graph_pendant_triple_expand, SimpleGraph.map_adj,
    SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]
