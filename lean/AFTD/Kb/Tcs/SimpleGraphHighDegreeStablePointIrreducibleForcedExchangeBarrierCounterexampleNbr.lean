import AFTD.Prelude

/-!
# simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_nbr

Topic: graphs   Node: d896ab4722fe

Provenance: helper lemma. step towards simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample

The neighbourhood bitmask of each vertex of the witness graph: bit w of entry v is set iff v and w are adjacent.
-/

/-- Neighbour bitmask representation of the witness graph; bit w of `nbr v` is set iff v is adjacent to w. -/
def simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_nbr : Fin 12 → Nat := ![4046, 3261, 4027, 3831, 3566, 1886, 4025, 3423, 3829, 1389, 3071, 1503]
