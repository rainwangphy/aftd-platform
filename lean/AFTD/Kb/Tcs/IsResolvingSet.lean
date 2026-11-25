import AFTD.Prelude

/-!
# is_resolving_set

Topic: graphs   Node: 568e0c2bf869

Provenance: formalization of a published result. Source: arXiv:2611.29819 Definition 1.1

A set S of vertices in a simple graph G is a resolving set if for every pair of distinct vertices u and v in G, there exists a vertex s in S such that the distance from u to s is not equal to the distance from v to s.
-/

/-- A subset S of vertices of a simple graph G is a resolving set if distinct vertices have different distances to some vertex in S. -/
def is_resolving_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ u v : V, u ≠ v → ∃ s ∈ S, G.dist u s ≠ G.dist v s
