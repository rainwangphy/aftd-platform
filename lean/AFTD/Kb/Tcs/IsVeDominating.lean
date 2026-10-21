import AFTD.Prelude

/-!
# is_ve_dominating

Topic: graphs   Node: d04ce59e8dc7

Provenance: formalization of a published result. Source: arXiv:2610.26912 Section 1

A subset S of vertices in a simple graph G is a vertex-edge dominating set if for all vertices x and y with G.Adj x y, there exists u in S such that u = x, or G.Adj u x, or u = y, or G.Adj u y.
-/

/-- A vertex set S is a vertex-edge dominating set if every edge has an endpoint in the closed neighborhood of some vertex in S. -/
def is_ve_dominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ ⦃x y : V⦄, G.Adj x y → ∃ u ∈ S, u = x ∨ G.Adj u x ∨ u = y ∨ G.Adj u y
