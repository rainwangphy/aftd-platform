import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.TenVertexExchangeFamilyEq
import AFTD.Kb.Tcs.TenVertexExchangeEdgeSet
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangeFamily

/-!
# ten_vertex_exchange_codegree

Topic: graphs   Node: 9b5be3c50f38

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

Each edge of the witness lies in at least three triangles.
-/

theorem ten_vertex_exchange_codegree : ∀ e ∈ ten_vertex_exchange_graph.edgeSet, 3 ≤ ((simple_graph_triangle_edge_family ten_vertex_exchange_graph).filter (fun t => e ∈ t)).card := by
  rw [ten_vertex_exchange_family_eq, ← ten_vertex_exchange_edge_set.1]
  decide
