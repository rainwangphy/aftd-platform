import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstStrategy

/-!
# stochastic_mst_strategy_cost

Topic: algorithms   Node: 2278ff4b7afc

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 3

For an edge probability function p assigning each edge e the probability that e has weight 1, the expected number of queries of a strategy is 0 at a leaf, and at a query node on edge e with children s₀ and s₁, it is 1 + (1 - p e) * cost(s₀) + p e * cost(s₁).
-/

/-- The expected number of queries made by an adaptive strategy under edge probability vector p. -/
def stochastic_mst_strategy_cost {α : Type*} (p : α → ℝ) : StochasticMstStrategy α → ℝ
| StochasticMstStrategy.leaf => 0
| StochasticMstStrategy.query e s₀ s₁ =>
    1 + (1 - p e) * stochastic_mst_strategy_cost p s₀ + p e * stochastic_mst_strategy_cost p s₁
