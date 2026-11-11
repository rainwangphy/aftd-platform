import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeTriangle

/-!
# ten_vertex_exchange_packing_q

Topic: graphs   Node: 3871b2a430c5

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The selected good ten-triangle packing.
-/

def ten_vertex_exchange_packing_q : Finset (Finset (Sym2 (Fin 10))) := {ten_vertex_exchange_triangle 0 1 2, ten_vertex_exchange_triangle 2 7 8, ten_vertex_exchange_triangle 3 4 7, ten_vertex_exchange_triangle 0 3 6, ten_vertex_exchange_triangle 4 6 8, ten_vertex_exchange_triangle 0 8 9, ten_vertex_exchange_triangle 5 6 9, ten_vertex_exchange_triangle 1 3 5, ten_vertex_exchange_triangle 2 3 9, ten_vertex_exchange_triangle 2 4 5}
