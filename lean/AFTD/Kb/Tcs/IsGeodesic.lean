import AFTD.Prelude

/-!
# is_geodesic

Topic: graphs   Node: 92b87e68961d

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 1

A walk p from u to v in a simple graph G is a geodesic if it is a simple path whose length equals the graph distance dist(u, v).
-/

/-- A walk in a simple graph is a geodesic if it is a path whose length equals the graph distance between its endpoints. -/
def is_geodesic {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Prop := p.IsPath ∧ p.length = G.dist u v
