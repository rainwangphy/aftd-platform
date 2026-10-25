import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPendantTripleExpand

/-!
# simple_graph_pendant_triple_expand_leaf_adj

Topic: graphs   Node: 39891433cae6

Provenance: helper lemma. Sanity lemma for simple_graph_pendant_triple_expand, the local reduction construction for OP-309.

Each added leaf is adjacent exactly to its corresponding fresh internal path vertex.
-/

theorem simple_graph_pendant_triple_expand_leaf_adj {V : Type*}
    (G : SimpleGraph V) (u v : V) (p : V ⊕ Fin 6) (i : Fin 3) :
    (simple_graph_pendant_triple_expand G u v).Adj p (Sum.inr (i.addNat 3)) ↔
      p = Sum.inr (i.castAdd 3) := by
  cases p with
  | inl a =>
    fin_cases i <;>
      simp [simple_graph_pendant_triple_expand, SimpleGraph.map_adj,
        SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]
  | inr j =>
    fin_cases i <;> fin_cases j <;>
      simp [simple_graph_pendant_triple_expand, SimpleGraph.map_adj,
        SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]
