import AFTD.Prelude

/-!
# maxcut_defect_one_nonoptimal_graph

Topic: equilibria   Node: 78b9ad4e1d55

Provenance: helper lemma. Graph found and independently verified in experiments 16395 and 16399.

An eight-vertex graph admitting a defect-one three-coloring although none of its optimal three-colorings is defect one.
-/

def maxcut_defect_one_nonoptimal_graph : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun u v : Fin 8 => (u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 6), (0, 7), (1, 2), (1, 5), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (4, 6), (5, 6), (6, 7)])
