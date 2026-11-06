import AFTD.Prelude
import AFTD.Kb.Tcs.VertexDisjointRoutingExists
import AFTD.Kb.Tcs.MixedGraphIsValidDirectedTriangle

/-!
# vertex_disjoint_routing_exists_zero

Topic: approximation   Node: 3603a4f7a1fe

Provenance: helper lemma. step towards weighted_spanning_tree_congestion_hardness_gap

With `p = 0` the disjoint-paths predicate holds, so it is not vacuously false.
-/

/-- Sanity witness for the disjoint-paths predicate: with no pairs there is nothing to route. -/
theorem vertex_disjoint_routing_exists_zero {V : Type*} (Q : SimpleGraph V) :
    vertex_disjoint_routing_exists Q (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) := by first | exact mixed_graph_is_valid_directed_triangle | (apply mixed_graph_is_valid_directed_triangle <;> assumption) | (apply mixed_graph_is_valid_directed_triangle <;> simp_all) | simpa using mixed_graph_is_valid_directed_triangle | (simp only [vertex_disjoint_routing_exists] at *; first | exact mixed_graph_is_valid_directed_triangle | (apply mixed_graph_is_valid_directed_triangle <;> assumption) | (apply mixed_graph_is_valid_directed_triangle <;> simp_all) | simpa using mixed_graph_is_valid_directed_triangle)
