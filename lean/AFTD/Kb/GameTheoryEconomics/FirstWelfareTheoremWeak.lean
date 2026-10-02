import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsWalrasianEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsWeaklyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy

/-!
# first_welfare_theorem_weak

Topic: general_equilibrium   Node: afc220b8fe6e

In a pure exchange economy E with finite, nonempty agent type Agent and finite commodity type Good, if price vector p : Good → ℝ has non-negative prices (∀ g, 0 ≤ p g) and allocation x : Agent → Good → ℝ forms a Walrasian equilibrium at prices p, then x is weakly Pareto optimal in E.
-/

/-- First Fundamental Theorem of Welfare Economics (weak form): any Walrasian equilibrium allocation with non-negative prices is weakly Pareto optimal. -/
theorem first_welfare_theorem_weak
    {Agent Good : Type*} [Fintype Agent] [Fintype Good] [Nonempty Agent]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ)
    (hp : ∀ g, 0 ≤ p g)
    (h_walras : is_walrasian_equilibrium E p x) :
    is_weakly_pareto_optimal E x := by
  constructor
  · exact h_walras.1
  · rintro ⟨y, hy_feas, hy_better⟩
    have h_budget_lt : ∀ i : Agent, ∑ g, p g * E.endowment i g < ∑ g, p g * y i g := by
      intro i
      by_contra! hle
      have h_le_utility := (h_walras.2 i).2 (y i) (hy_feas.1 i) hle
      have h_lt_utility := hy_better i
      exact lt_irrefl _ (h_lt_utility.trans_le h_le_utility)
    have h_sum_lt : ∑ i, ∑ g, p g * E.endowment i g < ∑ i, ∑ g, p g * y i g := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      exact h_budget_lt i
    rw [Finset.sum_comm] at h_sum_lt
    have h_comm_right : ∑ i, ∑ g, p g * y i g = ∑ g, ∑ i, p g * y i g := Finset.sum_comm
    rw [h_comm_right] at h_sum_lt
    have h_endow_eq : (∑ g, ∑ i, p g * E.endowment i g) = ∑ g, p g * ∑ i, E.endowment i g := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
    have h_y_eq : (∑ g, ∑ i, p g * y i g) = ∑ g, p g * ∑ i, y i g := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
    rw [h_endow_eq, h_y_eq] at h_sum_lt
    have h_sum_le : ∑ g, p g * ∑ i, y i g ≤ ∑ g, p g * ∑ i, E.endowment i g := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul_of_nonneg_left (hy_feas.2 g) (hp g)
    exact lt_irrefl _ (h_sum_lt.trans_le h_sum_le)
