import AFTD.Prelude

/-!
# simple_graph_is_perfect_dominating

Topic: graphs   Node: a7fd00755714

Provenance: formalization of a published result. Source: arXiv:2611.11191, Section 2

A subset D of vertices in a simple graph G is a perfect dominating set if every vertex v of G is dominated by exactly one vertex in D, that is, there exists a unique u in D such that u is adjacent to v or u equals v.
-/

/-- A subset D of vertices in a simple graph G is a perfect dominating set if every vertex is dominated by a unique element of D. -/
def simple_graph_is_perfect_dominating {V : Type*} (G : SimpleGraph V) (D : Set V) : Prop := ∀ v : V, ∃! u ∈ D, G.Adj v u ∨ v = u
