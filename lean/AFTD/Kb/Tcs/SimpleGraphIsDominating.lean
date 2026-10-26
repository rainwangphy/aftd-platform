import AFTD.Prelude

/-!
# simple_graph_is_dominating

Topic: graphs   Node: 8dc2fcedeaac

Provenance: formalization of a published result. Source: arXiv:2610.28936 Definition 2.1

A subset S of vertices in a simple graph G is a dominating set if every vertex of G is in S or is adjacent to a vertex in S.
-/

/-- Predicate that a set of vertices is a dominating set in a simple graph. -/
def simple_graph_is_dominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ v : V, v ∈ S ∨ ∃ u ∈ S, G.Adj u v
