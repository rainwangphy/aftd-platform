import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeCompleteFinFour
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# not_triangle_distinct_complete_fin_four

Topic: graphs   Node: 34c0300d3f04

Provenance: helper lemma. Sanity lemma for simple_graph_is_triangle_distinct (arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine)).

K_4 is not triangle-distinct.
-/

theorem not_triangle_distinct_complete_fin_four :
    ¬ simple_graph_is_triangle_distinct (⊤ : SimpleGraph (Fin 4)) := by
  intro h
  have := h ((simple_graph_triangle_degree_complete_fin_four 0).trans
    (simple_graph_triangle_degree_complete_fin_four 1).symm)
  exact absurd this (by decide)
