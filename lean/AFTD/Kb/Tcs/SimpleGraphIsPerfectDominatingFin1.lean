import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsPerfectDominating
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeCompleteFinFour

/-!
# simple_graph_is_perfect_dominating_fin1

Topic: graphs   Node: 6087dd51619c

Provenance: helper lemma. arXiv:2611.11191, Section 2

In the edgeless graph on one vertex, the singleton vertex set is a perfect dominating set.
-/

/-- Sanity check: the singleton vertex set of a one-vertex graph is a perfect dominating set. -/
theorem simple_graph_is_perfect_dominating_fin1 :
    simple_graph_is_perfect_dominating (⊥ : SimpleGraph (Fin 1)) {0} := by first | exact simple_graph_triangle_degree_complete_fin_four | (apply simple_graph_triangle_degree_complete_fin_four <;> assumption) | (apply simple_graph_triangle_degree_complete_fin_four <;> simp_all) | simpa using simple_graph_triangle_degree_complete_fin_four | (simp only [simple_graph_is_perfect_dominating] at *; first | exact simple_graph_triangle_degree_complete_fin_four | (apply simple_graph_triangle_degree_complete_fin_four <;> assumption) | (apply simple_graph_triangle_degree_complete_fin_four <;> simp_all) | simpa using simple_graph_triangle_degree_complete_fin_four)
