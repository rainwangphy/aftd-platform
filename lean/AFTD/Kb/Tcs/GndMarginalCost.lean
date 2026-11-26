import AFTD.Prelude

/-!
# gnd_marginal_cost

Topic: online_algorithms   Node: dfc87b8f0b68

Provenance: formalization of a published result. Source: arXiv:2611.30912 Section 2

The marginal increase in total power cost caused by assigning a request with weight vector w to a reply set reply ⊆ E under current load vector ℓ is ∑ e ∈ reply, (c e * (ℓ e + w e)^(pe e) - c e * (ℓ e)^(pe e)).
-/

/-- Marginal increase in power cost from assigning a request with weight w and reply set reply under current load ℓ. -/
noncomputable def gnd_marginal_cost {E : Type*} (c : E → ℝ) (pe : E → ℝ) (ℓ : E → ℝ) (w : E → ℝ) (reply : Finset E) : ℝ := ∑ e ∈ reply, (c e * (ℓ e + w e) ^ (pe e) - c e * (ℓ e) ^ (pe e))
