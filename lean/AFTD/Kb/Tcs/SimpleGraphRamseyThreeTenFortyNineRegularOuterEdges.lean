import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleFreeClosedNeighborhoodEdgeCount

/-!
# simple_graph_ramsey_three_ten_forty_nine_regular_outer_edges

Topic: combinatorics   Node: 606e402e108d

Provenance: helper lemma. step towards simple_graph_ramsey_three_ten_forty_of_max_degree_le_nine

In a 9-regular triangle-free simple graph on 40 vertices, for every vertex v the induced subgraph on the vertices outside the closed neighbourhood of v has exactly 99 edges.
-/

/-- For a 9-regular triangle-free 40-vertex graph, the subgraph induced outside any closed neighbourhood has exactly 99 edges. -/
theorem simple_graph_ramsey_three_ten_forty_nine_regular_outer_edges (g : SimpleGraph (Fin 40))
    [DecidableRel g.Adj] (htri : g.CliqueFree 3) (hreg : ∀ v, g.degree v = 9) (v : Fin 40) :
    (g.induce {u | u ≠ v ∧ ¬ g.Adj v u}).edgeFinset.card = 99 := by
  classical
  have hsum : (∑ u, g.degree u) = 360 := by simp [hreg]
  have htotal := g.sum_degrees_eq_twice_card_edges
  have hn : (∑ u ∈ g.neighborFinset v, g.degree u) = 81 := by
    simp [hreg, g.card_neighborFinset_eq_degree]
  have hed := simple_graph_triangle_free_closed_neighborhood_edge_count g htri v
  omega
