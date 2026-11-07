import AFTD.Prelude

/-!
# realization_prob

Topic: approximation   Node: 5a5b3e86cb06

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sec. 2

Given a simple graph G with finite edge set and edge probabilities p : G.edgeSet → ℝ, the probability of a binary edge weight realization α : G.edgeSet → Bool is the product over all edges e of (if α(e) then p(e) else 1 - p(e)).
-/

/-- The product Bernoulli probability of an edge realization α given marginal edge probabilities p. -/
noncomputable def realization_prob {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet]
    (p : G.edgeSet → ℝ) (α : G.edgeSet → Bool) : ℝ := ∏ e : G.edgeSet, if α e then p e else 1 - p e
