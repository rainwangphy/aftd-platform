import AFTD.Prelude

/-!
# digraph_is_vertex_transitive

Topic: graphs   Node: 88e6b9c001af

Provenance: formalization of a published result. Source: arXiv:2610.18600 Section 3

A directed graph G is vertex-transitive if for any two vertices u and v of G, there exists a graph automorphism of G mapping u to v.
-/

/-- A directed graph is vertex-transitive if its automorphism group acts transitively on its vertices. -/
def digraph_is_vertex_transitive {V : Type*} (G : Digraph V) : Prop := ∀ u v : V, ∃ e : G.Adj ≃r G.Adj, e u = v
