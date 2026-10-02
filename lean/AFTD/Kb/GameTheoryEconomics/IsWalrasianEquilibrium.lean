import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsFeasibleAllocation

/-!
# is_walrasian_equilibrium

Topic: general_equilibrium   Node: 321b97cdddb4

In a pure exchange economy E with finite agents Agent and finite commodities Good, a price vector p : Good → ℝ and an allocation x : Agent → Good → ℝ form a Walrasian (competitive) equilibrium if x is feasible in E, each agent's bundle x i satisfies the budget constraint ∑ g, p g * x i g ≤ ∑ g, p g * E.endowment i g, and for every agent i, any non-negative bundle y : Good → ℝ satisfying the budget constraint ∑ g, p g * y g ≤ ∑ g, p g * E.endowment i g satisfies E.utility i y ≤ E.utility i (x i).
-/

/-- A price vector `p` and allocation `x` constitute a Walrasian (competitive) equilibrium if `x` is feasible, each agent's bundle is affordable, and each agent maximizes utility over all affordable non-negative bundles. -/
def is_walrasian_equilibrium {Agent Good : Type*} [Fintype Agent] [Fintype Good]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ) : Prop := is_feasible_allocation E x ∧
  (∀ i, (∑ g, p g * x i g ≤ ∑ g, p g * E.endowment i g) ∧
    ∀ y : Good → ℝ, (∀ g, 0 ≤ y g) →
      (∑ g, p g * y g ≤ ∑ g, p g * E.endowment i g) →
      E.utility i y ≤ E.utility i (x i))
