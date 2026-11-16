import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMinor

/-!
# simple_graph_is_outerplanar

Topic: graphs   Node: 628f44c6cf9c

Provenance: formalization of a published result. Source: Chartrand and Harary (1967), Planar Permutation Graphs

A simple graph G is outerplanar (simple_graph_is_outerplanar G) if neither the complete graph on 4 vertices K_4 nor the complete bipartite graph K_{2,3} is a minor of G.
-/

/-- A simple graph G is outerplanar if neither K_4 nor K_{2,3} is a minor of G. -/
def simple_graph_is_outerplanar {V : Type*} (G : SimpleGraph V) : Prop := ¬ simple_graph_is_minor (⊤ : SimpleGraph (Fin 4)) G ∧
  ¬ simple_graph_is_minor (completeBipartiteGraph (Fin 2) (Fin 3)) G
