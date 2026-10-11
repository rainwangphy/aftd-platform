import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_triangle_degree_complete_fin_four

Topic: graphs   Node: 2ba720edd447

Provenance: helper lemma. Sanity lemma for simple_graph_triangle_degree (arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine)).

Every vertex of K_4 lies in exactly 3 triangles.
-/

theorem simple_graph_triangle_degree_complete_fin_four (v : Fin 4) :
    simple_graph_triangle_degree (⊤ : SimpleGraph (Fin 4)) v = 3 := by
  revert v; decide
