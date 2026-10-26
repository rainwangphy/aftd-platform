import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMinor

/-!
# simple_graph_is_planar

Topic: graphs   Node: a266349c3641

Provenance: formalization of a published result. Source: Wagner 1937; Diestel, Graph Theory (5th ed.), Theorem 4.4.2

A simple graph G is planar by Wagner's criterion if neither the complete graph on 5 vertices nor the complete bipartite graph K_{3,3} is a minor of G.
-/

/-- A graph is planar in the sense of Wagner if it contains neither K_5 nor K_{3,3} as a minor. -/
def simple_graph_is_planar {V : Type*} (G : SimpleGraph V) : Prop := ¬ simple_graph_is_minor (⊤ : SimpleGraph (Fin 5)) G ∧
  ¬ simple_graph_is_minor (completeBipartiteGraph (Fin 3) (Fin 3)) G
