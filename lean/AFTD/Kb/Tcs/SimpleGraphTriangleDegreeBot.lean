import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_triangle_degree_bot

Topic: graphs   Node: 49309f7b8d87

Provenance: helper lemma. Sanity lemma for simple_graph_triangle_degree (arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine)).

In the empty graph every vertex has triangle-degree 0.
-/

theorem simple_graph_triangle_degree_bot {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    simple_graph_triangle_degree (⊥ : SimpleGraph V) v = 0 := by
  simp [simple_graph_triangle_degree]
