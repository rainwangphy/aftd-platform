import AFTD.Prelude

/-!
# simple_graph_stable_conflict_independence_apex_edges

Topic: graphs   Node: 3bb4e3a3a8fd

Provenance: helper lemma. step towards simple_graph_stable_conflict_independence_counterexample

The ten edges at the apex vertex 0 of the counterexample graph, namely {0,1}, {0,2}, ..., {0,10}. These are exactly the edges of the packing support that are left unmarked.
-/

/-- The ten apex edges {0,v} for v = 1,...,10 of the counterexample graph. -/
def simple_graph_stable_conflict_independence_apex_edges : Finset (Sym2 (Fin 11)) := { Sym2.mk (0 : Fin 11) 1, Sym2.mk (0 : Fin 11) 2, Sym2.mk (0 : Fin 11) 3,
     Sym2.mk (0 : Fin 11) 4, Sym2.mk (0 : Fin 11) 5, Sym2.mk (0 : Fin 11) 6,
     Sym2.mk (0 : Fin 11) 7, Sym2.mk (0 : Fin 11) 8, Sym2.mk (0 : Fin 11) 9,
     Sym2.mk (0 : Fin 11) 10 }
