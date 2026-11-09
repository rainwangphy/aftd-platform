import AFTD.Prelude

/-!
# closed_neighbor_set

Topic: graphs   Node: 040839630eb0

Provenance: formalization of a published result. Source: arXiv:2611.09627:326

The closed neighborhood of a vertex set A in a graph G is the set of all vertices in A together with all vertices adjacent to at least one vertex of A.
-/

/-- The closed neighborhood of a subset A of vertices in a simple graph G is the union of A and the open neighborhoods of all vertices in A. -/
def closed_neighbor_set {V : Type*} (G : SimpleGraph V) (A : Set V) : Set V := {v | ∃ u ∈ A, v = u ∨ G.Adj u v}
