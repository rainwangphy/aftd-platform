import AFTD.Prelude

/-!
# triangle_link_exception_triangle_free_cubic

Topic: graphs   Node: f4caa15c8464

Provenance: helper lemma. arXiv:2610.15269, Section 3.1, and experiment 13077 for the 11-vertex extension.

The explicit 10-vertex connected subcubic exceptional link with edge set listed in the definition.
-/

def triangle_link_exception_triangle_free_cubic : SimpleGraph (Fin 10) := SimpleGraph.fromEdgeSet {s((0 : Fin 10), (3 : Fin 10)), s((0 : Fin 10), (6 : Fin 10)), s((0 : Fin 10), (9 : Fin 10)), s((1 : Fin 10), (4 : Fin 10)), s((1 : Fin 10), (6 : Fin 10)), s((1 : Fin 10), (8 : Fin 10)), s((2 : Fin 10), (5 : Fin 10)), s((2 : Fin 10), (6 : Fin 10)), s((2 : Fin 10), (7 : Fin 10)), s((3 : Fin 10), (7 : Fin 10)), s((3 : Fin 10), (8 : Fin 10)), s((4 : Fin 10), (7 : Fin 10)), s((4 : Fin 10), (9 : Fin 10)), s((5 : Fin 10), (8 : Fin 10)), s((5 : Fin 10), (9 : Fin 10))}
