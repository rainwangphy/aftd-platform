import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRamseyThreeTenNonregularEdgeBoundConditional
import AFTD.Kb.Tcs.SimpleGraphTriangleFreeClosedNeighborhoodEdgeCount

/-!
# simple_graph_ramsey_three_ten_forty_nine_regular_or_low_degree

Topic: combinatorics   Node: 0d26708ed19d

Provenance: helper lemma. step towards simple_graph_ramsey_three_ten_forty_of_max_degree_le_nine

A triangle-free simple graph on 40 vertices with maximum degree at most 9 is either 9-regular, or it has a vertex v of degree < 9 whose closed non-neighbourhood spans few edges: 2·e(outer) + 18·deg v ≤ 360.
-/

/-- Unconditional reduction: a triangle-free 40-vertex graph of maximum degree ≤ 9 is 9-regular or admits a low-degree vertex with an edge bound on its closed non-neighbourhood. -/
theorem simple_graph_ramsey_three_ten_forty_nine_regular_or_low_degree (G : SimpleGraph (Fin 40))
    [DecidableRel G.Adj] (htri : G.CliqueFree 3) (hmax : ∀ v, G.degree v ≤ 9) :
    (∀ v, G.degree v = 9) ∨
      ∃ v, G.degree v < 9 ∧
        2 * (G.induce {u | u ≠ v ∧ ¬ G.Adj v u}).edgeFinset.card + 18 * G.degree v ≤ 360 := by
  exact simple_graph_ramsey_three_ten_nonregular_edge_bound_conditional G htri hmax
    (fun v => simple_graph_triangle_free_closed_neighborhood_edge_count G htri v)
