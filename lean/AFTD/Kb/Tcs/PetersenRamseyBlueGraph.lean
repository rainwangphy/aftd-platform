import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenRamseyRedGraph

/-!
# petersen_ramsey_blue_graph

Topic: graphs   Node: 0fdf0d7d9da4

Provenance: formalization of a published result. Source: arXiv:2611.09347 Definition 1

The blue graph G_B on 20 vertices, defined as the graph complement of the red graph G_R, isomorphic to the join graph K_{9,9} ∨ K_2ᶜ.
-/

/-- The blue graph on 20 vertices, defined as the complement of the red graph G_R, isomorphic to the join K_{9,9} ∨ K_2ᶜ. -/
def petersen_ramsey_blue_graph : SimpleGraph (Fin 20) := petersen_ramsey_red_graphᶜ
