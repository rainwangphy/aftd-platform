import AFTD.Prelude

/-!
# simple_graph_max_degree_deleteEdges_le

Topic: graphs   Node: 85b43c61bca6

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number_of_max_degree_le_eleven

Deleting edges preserves maximum degree bounds: if every vertex has degree at most d, then deleting any set of edges preserves this bound.
-/

/-- Deleting edges preserves maximum degree bounds: if every vertex has degree at most d, then deleting any set of edges preserves this bound. -/
theorem simple_graph_max_degree_deleteEdges_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set (Sym2 V)) [DecidablePred (· ∈ s)] (d : ℕ)
    (h : ∀ v, G.degree v ≤ d) :
    ∀ v, (G.deleteEdges s).degree v ≤ d := by
  intro v
  exact le_trans (SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le s)) (h v)
