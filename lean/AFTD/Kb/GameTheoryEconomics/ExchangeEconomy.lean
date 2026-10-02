import AFTD.Prelude

/-!
# ExchangeEconomy

Topic: general_equilibrium   Node: 10d491c0b523

A pure exchange economy with agent type Agent and commodity type Good consists of a non-negative initial endowment of each good for each agent (endowment : Agent → Good → ℝ with endowment_nonneg : ∀ i g, 0 ≤ endowment i g) and a real-valued utility function over consumption bundles for each agent (utility : Agent → (Good → ℝ) → ℝ).
-/

/-- A pure exchange economy with agents `Agent` and commodities `Good`. -/
structure ExchangeEconomy (Agent Good : Type*) where
  endowment : Agent → Good → ℝ
  utility : Agent → (Good → ℝ) → ℝ
  endowment_nonneg : ∀ i g, 0 ≤ endowment i g
