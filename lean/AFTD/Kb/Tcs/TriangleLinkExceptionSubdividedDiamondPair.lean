import AFTD.Prelude

/-!
# triangle_link_exception_subdivided_diamond_pair

Topic: graphs   Node: 2e63bda490a8

Provenance: helper lemma. arXiv:2610.15269, Section 3.1, and experiment 13077 for the 11-vertex extension.

The explicit 11-vertex connected subcubic exceptional link with edge set listed in the definition.
-/

def triangle_link_exception_subdivided_diamond_pair : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet {s((0 : Fin 11), (4 : Fin 11)), s((0 : Fin 11), (8 : Fin 11)), s((1 : Fin 11), (5 : Fin 11)), s((1 : Fin 11), (9 : Fin 11)), s((1 : Fin 11), (10 : Fin 11)), s((2 : Fin 11), (6 : Fin 11)), s((2 : Fin 11), (7 : Fin 11)), s((2 : Fin 11), (8 : Fin 11)), s((3 : Fin 11), (6 : Fin 11)), s((3 : Fin 11), (7 : Fin 11)), s((3 : Fin 11), (8 : Fin 11)), s((4 : Fin 11), (9 : Fin 11)), s((4 : Fin 11), (10 : Fin 11)), s((5 : Fin 11), (9 : Fin 11)), s((5 : Fin 11), (10 : Fin 11)), s((6 : Fin 11), (7 : Fin 11))}
