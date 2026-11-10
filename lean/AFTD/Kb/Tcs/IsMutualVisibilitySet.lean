import AFTD.Prelude

/-!
# is_mutual_visibility_set

Topic: graphs   Node: c989e29a4204

Provenance: formalization of a published result. Source: arXiv:2611.09513, Section 1

A set S of vertices in a simple graph G is a mutual-visibility set if for every two distinct vertices u, v in S, there exists a shortest path between u and v whose internal vertices lie outside S.
-/

/-- A set `S` of vertices in a simple graph `G` is a mutual-visibility set if every two distinct vertices in `S` have a shortest path with all internal vertices outside `S`. -/
def is_mutual_visibility_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v →
  ∃ p : G.Walk u v, p.length = G.dist u v ∧ ∀ w ∈ p.support, w ∈ S → w = u ∨ w = v
