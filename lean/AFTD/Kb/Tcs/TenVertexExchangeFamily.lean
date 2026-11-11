import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeTriangle

/-!
# ten_vertex_exchange_family

Topic: graphs   Node: b74dff94bb38

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The explicit list of 52 triangle edge sets for the ten-vertex witness.
-/

def ten_vertex_exchange_family : Finset (Finset (Sym2 (Fin 10))) := {ten_vertex_exchange_triangle 0 1 2, ten_vertex_exchange_triangle 0 1 3, ten_vertex_exchange_triangle 0 1 7, ten_vertex_exchange_triangle 0 2 3, ten_vertex_exchange_triangle 0 2 7, ten_vertex_exchange_triangle 0 2 8, ten_vertex_exchange_triangle 0 2 9, ten_vertex_exchange_triangle 0 3 6, ten_vertex_exchange_triangle 0 3 7, ten_vertex_exchange_triangle 0 3 9, ten_vertex_exchange_triangle 0 6 7, ten_vertex_exchange_triangle 0 6 8, ten_vertex_exchange_triangle 0 6 9, ten_vertex_exchange_triangle 0 7 8, ten_vertex_exchange_triangle 0 8 9, ten_vertex_exchange_triangle 1 2 3, ten_vertex_exchange_triangle 1 2 4, ten_vertex_exchange_triangle 1 2 5, ten_vertex_exchange_triangle 1 2 7, ten_vertex_exchange_triangle 1 3 4, ten_vertex_exchange_triangle 1 3 5, ten_vertex_exchange_triangle 1 3 7, ten_vertex_exchange_triangle 1 4 5, ten_vertex_exchange_triangle 1 4 7, ten_vertex_exchange_triangle 2 3 4, ten_vertex_exchange_triangle 2 3 5, ten_vertex_exchange_triangle 2 3 7, ten_vertex_exchange_triangle 2 3 9, ten_vertex_exchange_triangle 2 4 5, ten_vertex_exchange_triangle 2 4 7, ten_vertex_exchange_triangle 2 4 8, ten_vertex_exchange_triangle 2 5 8, ten_vertex_exchange_triangle 2 5 9, ten_vertex_exchange_triangle 2 7 8, ten_vertex_exchange_triangle 2 8 9, ten_vertex_exchange_triangle 3 4 5, ten_vertex_exchange_triangle 3 4 6, ten_vertex_exchange_triangle 3 4 7, ten_vertex_exchange_triangle 3 5 6, ten_vertex_exchange_triangle 3 5 9, ten_vertex_exchange_triangle 3 6 7, ten_vertex_exchange_triangle 3 6 9, ten_vertex_exchange_triangle 4 5 6, ten_vertex_exchange_triangle 4 5 8, ten_vertex_exchange_triangle 4 6 7, ten_vertex_exchange_triangle 4 6 8, ten_vertex_exchange_triangle 4 7 8, ten_vertex_exchange_triangle 5 6 8, ten_vertex_exchange_triangle 5 6 9, ten_vertex_exchange_triangle 5 8 9, ten_vertex_exchange_triangle 6 7 8, ten_vertex_exchange_triangle 6 8 9}
