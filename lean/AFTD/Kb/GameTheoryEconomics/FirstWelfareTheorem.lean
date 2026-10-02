import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsWalrasianEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimal
import AFTD.Kb.GameTheoryEconomics.WalrasianExpenditureGtOfUtilityGt
import AFTD.Kb.GameTheoryEconomics.WalrasianExpenditureGeOfUtilityGe

/-!
# first_welfare_theorem

Topic: general_equilibrium   Node: 3b9432239b8d

The First Fundamental Theorem of Welfare Economics: in a pure exchange economy E with finite, nonempty agent type Agent and finite, nonempty commodity type Good, if price vector p has strictly positive prices, every agent has a strictly monotone utility function, and (p, x) is a Walrasian equilibrium in E, then the allocation x is Pareto optimal in E.
-/

/-- First Fundamental Theorem of Welfare Economics: every Walrasian equilibrium allocation is Pareto optimal under strictly monotone utilities and strictly positive prices. -/
theorem first_welfare_theorem
    {Agent Good : Type*} [Fintype Agent] [Fintype Good] [Nonempty Agent] [Nonempty Good]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ)
    (hp : ∀ g, 0 < p g)
    (h_mono : ∀ i, StrictMono (E.utility i))
    (h_walras : is_walrasian_equilibrium E p x) :
    is_pareto_optimal E x := by
  constructor
  · exact h_walras.1
  · rintro ⟨y, hy_feas, hy_ge, ⟨i0, hi0⟩⟩
    have h_budget_ge : ∀ i : Agent, ∑ g, p g * E.endowment i g ≤ ∑ g, p g * y i g := by
      intro i
      exact walrasian_expenditure_ge_of_utility_ge E p x i hp (h_mono i) h_walras (y i) (hy_feas.1 i) (hy_ge i)
    have h_budget_gt : ∑ g, p g * E.endowment i0 g < ∑ g, p g * y i0 g := by
      exact walrasian_expenditure_gt_of_utility_gt E p x h_walras i0 (y i0) (hy_feas.1 i0) hi0
    have h_sum_lt : ∑ i, ∑ g, p g * E.endowment i g < ∑ i, ∑ g, p g * y i g := by
      apply Finset.sum_lt_sum
      · intro i _
        exact h_budget_ge i
      · exact ⟨i0, Finset.mem_univ i0, h_budget_gt⟩
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
      exact mul_le_mul_of_nonneg_left (hy_feas.2 g) (le_of_lt (hp g))
    exact lt_irrefl _ (h_sum_lt.trans_le h_sum_le)
