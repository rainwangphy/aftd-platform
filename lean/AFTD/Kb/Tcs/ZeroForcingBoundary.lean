import AFTD.Prelude

/-!
# zero_forcing_boundary

Topic: graphs   Node: 0f30c21a59da

Provenance: formalization of a published result. Source: arXiv:2611.13244, Definition 2.8 -- Stabilization of the zero forcing number of generalized Petersen graphs

For a simple graph G and a subset X of vertices, the boundary ∂X is the set of all vertices x in X that have a neighbor outside X.
-/

/-- The boundary of a vertex subset X in a graph G is the set of vertices in X with at least one neighbor outside X. -/
def zero_forcing_boundary {V : Type*} (G : SimpleGraph V) (X : Set V) : Set V := {x ∈ X | ∃ y ∈ G.neighborSet x, y ∉ X}
