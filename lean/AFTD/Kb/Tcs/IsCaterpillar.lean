import AFTD.Prelude

/-!
# is_caterpillar

Topic: graphs   Node: 09cbf866ddf8

Provenance: formalization of a published result. Source: arXiv:2610.31785 Section 2.2; Harary-Schwenk 1973

A graph is a caterpillar if it is a tree containing a path such that every vertex is either on the path or adjacent to a vertex on the path.
-/

/-- A caterpillar is a tree that contains a path such that every vertex is on the path or adjacent to a vertex on the path. -/
def is_caterpillar {V : Type*} (G : SimpleGraph V) : Prop := G.IsTree ∧ ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ w : V, w ∈ p.support ∨ ∃ z ∈ p.support, G.Adj w z
