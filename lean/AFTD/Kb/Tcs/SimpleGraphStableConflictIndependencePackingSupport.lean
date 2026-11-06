import AFTD.Prelude

/-!
# simple_graph_stable_conflict_independence_packing_support

Topic: graphs   Node: d16636d8a87f

Provenance: helper lemma. step towards simple_graph_stable_conflict_independence_counterexample

The 15-edge support of the five-triangle packing P = {{0,1,3},{0,2,9},{0,4,6},{0,5,7},{0,8,10}}: all ten apex edges together with the five marked base edges {1,3}, {2,9}, {4,6}, {5,7}, {8,10}.
-/

/-- The 15-edge union of the five packed triangles of the counterexample. -/
def simple_graph_stable_conflict_independence_packing_support : Finset (Sym2 (Fin 11)) := { Sym2.mk (0 : Fin 11) 1, Sym2.mk (0 : Fin 11) 2, Sym2.mk (0 : Fin 11) 3,
     Sym2.mk (0 : Fin 11) 4, Sym2.mk (0 : Fin 11) 5, Sym2.mk (0 : Fin 11) 6,
     Sym2.mk (0 : Fin 11) 7, Sym2.mk (0 : Fin 11) 8, Sym2.mk (0 : Fin 11) 9,
     Sym2.mk (0 : Fin 11) 10, Sym2.mk (1 : Fin 11) 3, Sym2.mk (2 : Fin 11) 9,
     Sym2.mk (4 : Fin 11) 6, Sym2.mk (5 : Fin 11) 7, Sym2.mk (8 : Fin 11) 10 }
