import AFTD.Prelude

/-!
# simple_graph_three_vertex_connected

Topic: graphs   Node: 84b384709eb5

Provenance: formalization of a published result. Source: Standard k-connectivity (Diestel, Graph Theory, Sec. 1.4) with k = 3, as used in OP-541; arXiv:2610.25886 (Extremal arborescences in graph orientations)

A simple graph on Fin n is 3-vertex-connected if it has at least 4 vertices and deleting any set of at most 2 vertices leaves a connected graph.
-/

/-- G is 3-vertex-connected: at least 4 vertices, and connected after deleting any at most 2 vertices. -/
def simple_graph_three_vertex_connected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  4 ≤ n ∧ ∀ X : Finset (Fin n), X.card ≤ 2 → (G.induce ((X : Set (Fin n))ᶜ)).Connected
