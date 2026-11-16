import AFTD.Prelude

/-!
# simple_graph_is_equitable_coloring

Topic: graphs   Node: b3d5ec73cc60

Provenance: formalization of a published result. Source: arXiv:2611.18391, Section 2

A coloring c : V → α of a finite simple graph G is equitable (simple_graph_is_equitable_coloring G c) if for all vertices u and v with c u = c v and every color j : α, u and v have the same number of neighbors of color j in G.
-/

/-- A vertex coloring of a finite graph is equitable if vertices of the same color have the same number of neighbors of each color. -/
def simple_graph_is_equitable_coloring {V α : Type*} [Fintype V] (G : SimpleGraph V) (c : V → α) : Prop := ∀ u v : V, c u = c v → ∀ j : α,
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableEq α := Classical.decEq _
  ((G.neighborFinset u).filter (fun w => c w = j)).card =
  ((G.neighborFinset v).filter (fun w => c w = j)).card
