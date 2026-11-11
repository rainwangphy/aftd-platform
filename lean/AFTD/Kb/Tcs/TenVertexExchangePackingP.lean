import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeTriangle

/-!
# ten_vertex_exchange_packing_p

Topic: graphs   Node: d5c5b2f0e301

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The selected ten-triangle packing in the local exchange trap.
-/

def ten_vertex_exchange_packing_p : Finset (Finset (Sym2 (Fin 10))) := {ten_vertex_exchange_triangle 3 4 5, ten_vertex_exchange_triangle 0 2 7, ten_vertex_exchange_triangle 0 3 6, ten_vertex_exchange_triangle 0 8 9, ten_vertex_exchange_triangle 5 6 9, ten_vertex_exchange_triangle 1 2 4, ten_vertex_exchange_triangle 6 7 8, ten_vertex_exchange_triangle 1 3 7, ten_vertex_exchange_triangle 2 3 9, ten_vertex_exchange_triangle 2 5 8}
