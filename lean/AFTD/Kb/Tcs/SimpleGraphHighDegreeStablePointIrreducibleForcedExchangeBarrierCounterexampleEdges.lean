import AFTD.Prelude

/-!
# simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_edges

Topic: graphs   Node: 93ab4d601fb4

Provenance: helper lemma. step towards simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample

The 54 edges of the witness graph on Fin 12, listed explicitly as unordered vertex pairs.
-/

/-- The 54 edges of the witness graph. -/
def simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_edges : Finset (Sym2 (Fin 12)) := (([Sym2.mk 0 1, Sym2.mk 0 2, Sym2.mk 0 3, Sym2.mk 0 6, Sym2.mk 0 7, Sym2.mk 0 8, Sym2.mk 0 9, Sym2.mk 0 10, Sym2.mk 0 11, Sym2.mk 1 2, Sym2.mk 1 3, Sym2.mk 1 4, Sym2.mk 1 5, Sym2.mk 1 7, Sym2.mk 1 10, Sym2.mk 1 11, Sym2.mk 2 3, Sym2.mk 2 4, Sym2.mk 2 5, Sym2.mk 2 7, Sym2.mk 2 8, Sym2.mk 2 9, Sym2.mk 2 10, Sym2.mk 2 11, Sym2.mk 3 4, Sym2.mk 3 5, Sym2.mk 3 6, Sym2.mk 3 7, Sym2.mk 3 9, Sym2.mk 3 10, Sym2.mk 3 11, Sym2.mk 4 5, Sym2.mk 4 6, Sym2.mk 4 7, Sym2.mk 4 8, Sym2.mk 4 10, Sym2.mk 4 11, Sym2.mk 5 6, Sym2.mk 5 8, Sym2.mk 5 9, Sym2.mk 5 10, Sym2.mk 6 7, Sym2.mk 6 8, Sym2.mk 6 9, Sym2.mk 6 10, Sym2.mk 6 11, Sym2.mk 7 8, Sym2.mk 7 10, Sym2.mk 7 11, Sym2.mk 8 9, Sym2.mk 8 10, Sym2.mk 8 11, Sym2.mk 9 10, Sym2.mk 10 11] : List (Sym2 (Fin 12))).toFinset)
