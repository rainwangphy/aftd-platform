import AFTD.Prelude

/-!
# is_edge_geodesic_transversal

Topic: graphs   Node: 0a192fea22f8

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 1

A finite set S of edges of G is an edge geodesic transversal if every maximal geodesic in G contains at least one edge of S.
-/

/-- A finite set of edges S in G is an edge geodesic transversal if every maximal geodesic of G contains at least one edge of S. -/
def is_edge_geodesic_transversal {V : Type*} (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop := (∀ e ∈ S, e ∈ G.edgeSet) ∧
  ∀ ⦃u v : V⦄ (p : G.Walk u v),
    (p.IsPath ∧ p.length = G.dist u v ∧
      (∀ w, G.Adj w u → G.dist w v ≤ p.length) ∧
      (∀ w, G.Adj v w → G.dist u w ≤ p.length)) →
    ∃ e ∈ S, e ∈ p.edges
