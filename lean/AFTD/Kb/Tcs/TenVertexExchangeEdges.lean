import AFTD.Prelude

/-!
# ten_vertex_exchange_edges

Topic: graphs   Node: 4f228b6c17fd

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The 35 unordered edges of the explicit ten-vertex witness.
-/

open scoped Sym2

def ten_vertex_exchange_edges : Finset (Sym2 (Fin 10)) := {s(0,1), s(0,2), s(0,3), s(0,6), s(0,7), s(0,8), s(0,9), s(1,2), s(1,3), s(1,4), s(1,5), s(1,7), s(2,3), s(2,4), s(2,5), s(2,7), s(2,8), s(2,9), s(3,4), s(3,5), s(3,6), s(3,7), s(3,9), s(4,5), s(4,6), s(4,7), s(4,8), s(5,6), s(5,8), s(5,9), s(6,7), s(6,8), s(6,9), s(7,8), s(8,9)}
