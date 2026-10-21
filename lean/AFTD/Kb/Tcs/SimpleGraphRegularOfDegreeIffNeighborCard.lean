import AFTD.Prelude

/-!
# simple_graph_regular_of_degree_iff_neighbor_card

Topic: graphs   Node: d0d761f3aaa0

Provenance: helper lemma. step towards exists_nonempty_regular_eight_triangle_distinct

A finite simple graph is regular of degree d if and only if every vertex has exactly d neighbours, counted as the cardinality of its neighbour finset.
-/

/-- Regularity of a finite graph is decided by the cardinalities of its neighbour finsets. -/
theorem simple_graph_regular_of_degree_iff_neighbor_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    G.IsRegularOfDegree d ↔ ∀ v : V, (G.neighborFinset v).card = d := by
  simp_rw [SimpleGraph.IsRegularOfDegree, SimpleGraph.card_neighborFinset_eq_degree]
