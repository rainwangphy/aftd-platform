import AFTD.Prelude

/-!
# op874_twelve_vertex_no_matching_cut_edges

Topic: graphs   Node: 57c9539fb655

Provenance: helper lemma. Explicit 12-vertex obstruction to the OP-874 perfect-matching-cut route, experiment 35469.

The eighteen edges of the displayed twelve-vertex cubic graph.
-/

def op874_twelve_vertex_no_matching_cut_edges : Finset (Sym2 (Fin 12)) := {s((0 : Fin 12), (2 : Fin 12)), s((0 : Fin 12), (8 : Fin 12)), s((0 : Fin 12), (11 : Fin 12)), s((1 : Fin 12), (7 : Fin 12)), s((1 : Fin 12), (8 : Fin 12)), s((1 : Fin 12), (10 : Fin 12)), s((2 : Fin 12), (5 : Fin 12)), s((2 : Fin 12), (7 : Fin 12)), s((3 : Fin 12), (6 : Fin 12)), s((3 : Fin 12), (7 : Fin 12)), s((3 : Fin 12), (9 : Fin 12)), s((4 : Fin 12), (5 : Fin 12)), s((4 : Fin 12), (6 : Fin 12)), s((4 : Fin 12), (8 : Fin 12)), s((5 : Fin 12), (9 : Fin 12)), s((6 : Fin 12), (10 : Fin 12)), s((9 : Fin 12), (11 : Fin 12)), s((10 : Fin 12), (11 : Fin 12))}
