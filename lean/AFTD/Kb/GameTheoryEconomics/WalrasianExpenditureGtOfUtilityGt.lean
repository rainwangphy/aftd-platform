import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsWalrasianEquilibrium

/-!
# walrasian_expenditure_gt_of_utility_gt

Topic: general_equilibrium   Node: 5869371c90ca

In a pure exchange economy E with finite agents Agent and finite commodities Good, if (p, x) is a Walrasian equilibrium, then for any agent i and any non-negative consumption bundle y such that agent i strictly prefers y to x_i (that is, E.utility i (x i) < E.utility i y), the market expenditure on y strictly exceeds the value of agent i's initial endowment (that is, ∑ g, p g * E.endowment i g < ∑ g, p g * y g).
-/

/-- In a Walrasian equilibrium, any non-negative bundle giving strictly greater utility costs strictly more than the agent's endowment. -/
theorem walrasian_expenditure_gt_of_utility_gt
    {Agent Good : Type*} [Fintype Agent] [Fintype Good]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ)
    (h_walras : is_walrasian_equilibrium E p x) (i : Agent)
    (y : Good → ℝ) (hy_nonneg : ∀ g, 0 ≤ y g)
    (hy_u : E.utility i (x i) < E.utility i y) :
    ∑ g, p g * E.endowment i g < ∑ g, p g * y g := by
  by_contra h_not
  have h_le : ∑ g, p g * y g ≤ ∑ g, p g * E.endowment i g := le_of_not_gt h_not
  have h_opt := h_walras.2 i
  have h_u_le := h_opt.2 y hy_nonneg h_le
  exact not_le_of_gt hy_u h_u_le
