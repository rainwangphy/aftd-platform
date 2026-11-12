import AFTD.Prelude

/-!
# is_uniquely_clique_saturated

Topic: graphs   Node: 8c6e6fd9b8ef

Provenance: formalization of a published result. Source: arXiv:2611.13656 Section 1

A simple graph G is uniquely K_r-saturated if it contains no clique of size r, but adding any non-edge e to G creates exactly one clique of size r.
-/

/-- A simple graph is uniquely K_r-saturated if it has no r-clique, but adding any non-edge produces a unique r-clique. -/
def is_uniquely_clique_saturated {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  (∀ s : Finset V, ¬ G.IsNClique r s) ∧
  (∀ e ∈ Gᶜ.edgeSet, ∃! s : Finset V, (G ⊔ SimpleGraph.fromEdgeSet {e}).IsNClique r s)
