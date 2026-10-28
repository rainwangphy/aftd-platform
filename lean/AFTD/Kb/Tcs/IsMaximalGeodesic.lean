import AFTD.Prelude

/-!
# is_maximal_geodesic

Topic: graphs   Node: 7bb02da04aa0

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 1

A geodesic p from u to v is maximal if no adjacent vertex at either endpoint extends it to a strictly longer geodesic.
-/

/-- A walk is a maximal geodesic if it is a geodesic that cannot be extended at either endpoint. -/
def is_maximal_geodesic {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Prop := (p.IsPath ∧ p.length = G.dist u v) ∧
  (∀ w, G.Adj w u → G.dist w v ≤ p.length) ∧
  (∀ w, G.Adj v w → G.dist u w ≤ p.length)
