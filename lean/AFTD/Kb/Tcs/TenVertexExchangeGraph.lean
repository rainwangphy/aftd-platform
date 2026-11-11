import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeEdges

/-!
# ten_vertex_exchange_graph

Topic: graphs   Node: 614df29e6730

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The simple graph built from the explicit ten-vertex edge set.
-/

def ten_vertex_exchange_graph : SimpleGraph (Fin 10) := SimpleGraph.fromEdgeSet (↑ten_vertex_exchange_edges : Set (Sym2 (Fin 10)))
