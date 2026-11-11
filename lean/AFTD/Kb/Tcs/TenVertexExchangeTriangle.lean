import AFTD.Prelude

/-!
# ten_vertex_exchange_triangle

Topic: graphs   Node: 6ad45fe06602

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

The three edges of a triangle on specified vertices.
-/

open scoped Sym2

def ten_vertex_exchange_triangle (a b c : Fin 10) : Finset (Sym2 (Fin 10)) := {s(a,b),s(a,c),s(b,c)}
