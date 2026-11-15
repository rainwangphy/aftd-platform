import AFTD.Prelude

/-!
# optimal_tour_length

Topic: graphs   Node: 2911d6012211

Provenance: formalization of a published result. Source: arXiv:2611.14755, Section 2

The optimal tour length in an edge-weighted simple graph (G, w) is the infimum of the sum of edge weights over all closed walks that visit every vertex of G.
-/

/-- The minimum length of a closed walk visiting all vertices in an edge-weighted graph (G, w). -/
noncomputable def optimal_tour_length {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  sInf { (p.edges.map w).sum | (u : V) (p : G.Walk u u) (_ : ∀ v, v ∈ p.support) }
