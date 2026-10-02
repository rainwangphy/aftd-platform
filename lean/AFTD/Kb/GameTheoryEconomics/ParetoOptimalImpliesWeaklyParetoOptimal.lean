import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimal
import AFTD.Kb.GameTheoryEconomics.IsWeaklyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy

/-!
# pareto_optimal_implies_weakly_pareto_optimal

Topic: general_equilibrium   Node: 33c4aacc08dc

In a pure exchange economy E with finite, nonempty agent type Agent, if an allocation x : Agent → Good → ℝ is Pareto optimal in E, then x is weakly Pareto optimal in E.
-/

/-- In a pure exchange economy with at least one agent, any Pareto optimal allocation is weakly Pareto optimal. -/
theorem pareto_optimal_implies_weakly_pareto_optimal
    {Agent Good : Type*} [Fintype Agent] [Nonempty Agent]
    (E : ExchangeEconomy Agent Good) (x : Agent → Good → ℝ)
    (h : is_pareto_optimal E x) :
    is_weakly_pareto_optimal E x := by
  rcases h with ⟨hfeas, hnot⟩
  refine ⟨hfeas, ?_⟩
  rintro ⟨y, hyfeas, hy⟩
  apply hnot
  obtain ⟨i₀⟩ := ‹Nonempty Agent›
  exact ⟨y, hyfeas, fun i => (hy i).le, ⟨i₀, hy i₀⟩⟩
