import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStrongEdgeColoring

/-!
# simple_graph_is_strong_edge_coloring_of_injective

Topic: graphs   Node: 5d6c2ddbc512

Provenance: helper lemma. sanity lemma for simple_graph_is_strong_edge_coloring

Sanity: a colouring giving all pairs distinct colours is a strong edge-colouring.
-/

theorem simple_graph_is_strong_edge_coloring_of_injective {W Ω : Type*} (G : SimpleGraph W)
    (χ : Sym2 W → Ω) (hχ : Function.Injective χ) : simple_graph_is_strong_edge_coloring G χ :=
  fun _ _ _ _ hxy _ heq => hxy (hχ heq)
