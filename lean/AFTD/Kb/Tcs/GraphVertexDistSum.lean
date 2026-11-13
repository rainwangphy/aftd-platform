import AFTD.Prelude

/-!
# graph_vertex_dist_sum

Topic: graphs   Node: 63bdd0337c69

Provenance: formalization of a published result. Source: arXiv:2611.12781, Section 2, equation (169)

For a vertex u in a finite simple graph G on vertex type V, graph_vertex_dist_sum G u is the sum ∑ v : V, G.dist u v of shortest-path distances from u to all vertices v of G.
-/

/-- The sum of shortest-path distances from vertex u to all vertices in G. -/
noncomputable def graph_vertex_dist_sum {V : Type*} [Fintype V] (G : SimpleGraph V) (u : V) : ℕ := ∑ v : V, G.dist u v
