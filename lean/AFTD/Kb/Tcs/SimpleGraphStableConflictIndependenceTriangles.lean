import AFTD.Prelude

/-!
# simple_graph_stable_conflict_independence_triangles

Topic: graphs   Node: dbd82bce2aaa

Provenance: helper lemma. step towards simple_graph_stable_conflict_independence_counterexample

The explicit family of 19 triangles of the 11-vertex counterexample graph: the 17 apex triangles {0,a,b} indexed by the base edges {a,b} of the 10-vertex base graph, together with the two leaf triangles {1,3,7} and {1,5,7}.
-/

/-- The 19 triangles (17 apex triangles through vertex 0 plus the two leaves {1,3,7}, {1,5,7}) of the counterexample graph. -/
def simple_graph_stable_conflict_independence_triangles : Finset (Finset (Sym2 (Fin 11))) := { {Sym2.mk (0 : Fin 11) 1, Sym2.mk (0 : Fin 11) 3, Sym2.mk (1 : Fin 11) 3},
     {Sym2.mk (0 : Fin 11) 1, Sym2.mk (0 : Fin 11) 5, Sym2.mk (1 : Fin 11) 5},
     {Sym2.mk (0 : Fin 11) 1, Sym2.mk (0 : Fin 11) 7, Sym2.mk (1 : Fin 11) 7},
     {Sym2.mk (0 : Fin 11) 2, Sym2.mk (0 : Fin 11) 6, Sym2.mk (2 : Fin 11) 6},
     {Sym2.mk (0 : Fin 11) 2, Sym2.mk (0 : Fin 11) 8, Sym2.mk (2 : Fin 11) 8},
     {Sym2.mk (0 : Fin 11) 2, Sym2.mk (0 : Fin 11) 9, Sym2.mk (2 : Fin 11) 9},
     {Sym2.mk (0 : Fin 11) 3, Sym2.mk (0 : Fin 11) 7, Sym2.mk (3 : Fin 11) 7},
     {Sym2.mk (0 : Fin 11) 3, Sym2.mk (0 : Fin 11) 9, Sym2.mk (3 : Fin 11) 9},
     {Sym2.mk (0 : Fin 11) 3, Sym2.mk (0 : Fin 11) 10, Sym2.mk (3 : Fin 11) 10},
     {Sym2.mk (0 : Fin 11) 4, Sym2.mk (0 : Fin 11) 6, Sym2.mk (4 : Fin 11) 6},
     {Sym2.mk (0 : Fin 11) 4, Sym2.mk (0 : Fin 11) 8, Sym2.mk (4 : Fin 11) 8},
     {Sym2.mk (0 : Fin 11) 4, Sym2.mk (0 : Fin 11) 9, Sym2.mk (4 : Fin 11) 9},
     {Sym2.mk (0 : Fin 11) 5, Sym2.mk (0 : Fin 11) 7, Sym2.mk (5 : Fin 11) 7},
     {Sym2.mk (0 : Fin 11) 5, Sym2.mk (0 : Fin 11) 9, Sym2.mk (5 : Fin 11) 9},
     {Sym2.mk (0 : Fin 11) 5, Sym2.mk (0 : Fin 11) 10, Sym2.mk (5 : Fin 11) 10},
     {Sym2.mk (0 : Fin 11) 6, Sym2.mk (0 : Fin 11) 10, Sym2.mk (6 : Fin 11) 10},
     {Sym2.mk (0 : Fin 11) 8, Sym2.mk (0 : Fin 11) 10, Sym2.mk (8 : Fin 11) 10},
     {Sym2.mk (1 : Fin 11) 3, Sym2.mk (1 : Fin 11) 7, Sym2.mk (3 : Fin 11) 7},
     {Sym2.mk (1 : Fin 11) 5, Sym2.mk (1 : Fin 11) 7, Sym2.mk (5 : Fin 11) 7} }
