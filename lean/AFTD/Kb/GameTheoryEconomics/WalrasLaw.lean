import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy

/-!
# walras_law

Topic: general_equilibrium   Node: a1bc12b19938

In a pure exchange economy E with finite agents Agent and finite commodities Good, if an allocation x : Agent → Good → ℝ satisfies budget exhaustion at price vector p : Good → ℝ (that is, for every agent i, ∑ g, p g * x i g = ∑ g, p g * E.endowment i g), then the total market value of aggregate excess demand is zero: ∑ g, p g * (∑ i, x i g - ∑ i, E.endowment i g) = 0.
-/

/-- Walras' Law: if every agent exhausts their budget constraint at price vector `p`, the total market value of aggregate excess demand is zero. -/
theorem walras_law {Agent Good : Type*} [Fintype Agent] [Fintype Good]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ)
    (h_budget : ∀ i, ∑ g, p g * x i g = ∑ g, p g * E.endowment i g) :
    ∑ g, p g * (∑ i, x i g - ∑ i, E.endowment i g) = 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g i => p g * E.endowment i g)]
  simp_rw [h_budget, sub_self]
