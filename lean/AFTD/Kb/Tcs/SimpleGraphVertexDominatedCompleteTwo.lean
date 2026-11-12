import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphVertexDominated

/-!
# simple_graph_vertex_dominated_complete_two

Topic: graphs   Node: 3c687518cd1f

Provenance: helper lemma. arXiv:2611.14430 Section 2

In the complete graph on two vertices, vertex 0 is dominated.
-/

/-- In the complete graph on two vertices, vertex 0 is dominated by vertex 1. -/
theorem simple_graph_vertex_dominated_complete_two :
    simple_graph_vertex_dominated (⊤ : SimpleGraph (Fin 2)) (0 : Fin 2) := by
  use 1
  refine ⟨by decide, ?_⟩
  intro x _
  fin_cases x
  · right
    simp
  · left
    rfl
