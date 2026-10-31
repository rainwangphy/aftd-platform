import AFTD.Prelude

/-!
# graph_is_mutual_visibility_set

Topic: graphs   Node: 759b6e153aec

Provenance: formalization of a published result. Source: arXiv:2610.39430, Definition 1.1

A set S of vertices of a simple graph G is a mutual-visibility set if for every pair of vertices u, v in S, there exists a shortest walk from u to v in G such that every vertex on the walk that belongs to S is either u or v.
-/

/-- A set S of vertices of G is a mutual-visibility set if every pair in S is joined by a shortest walk whose internal vertices avoid S. -/
def graph_is_mutual_visibility_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ u ∈ S, ∀ v ∈ S, ∃ p : G.Walk u v, p.length = G.dist u v ∧
    ∀ x ∈ p.support, x ∈ S → x = u ∨ x = v
