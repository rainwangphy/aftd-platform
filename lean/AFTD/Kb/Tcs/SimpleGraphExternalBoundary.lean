import AFTD.Prelude

/-!
# simple_graph_external_boundary

Topic: graphs   Node: d8b467363708

Provenance: formalization of a published result. Source: arXiv:2610.24059

The external vertex boundary of a vertex set S in a graph G is the set of all vertices outside S adjacent to at least one vertex in S.
-/

/-- The external vertex boundary of a vertex set S in a simple graph G. -/
def simple_graph_external_boundary {V : Type*} (G : SimpleGraph V) (S : Set V) : Set V := {w | w ∉ S ∧ ∃ u ∈ S, G.Adj u w}
