import AFTD.Prelude

/-!
# OMSRArrival

Topic: online_algorithms   Node: bc6f146e3aa9

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:405

An arrival in online bipartite matching with stochastic rewards and patience facing n offline resources, consisting of a patience budget of at least 1 and probe success probabilities in [0, 1].
-/

/-- An arrival in online matching with stochastic rewards and patience facing n offline resources. -/
structure OMSRArrival (n : ℕ) where
  patience : ℕ
  patience_pos : 1 ≤ patience
  prob : Fin n → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_le_one : ∀ i, prob i ≤ 1
