import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsFeasibleAllocation

/-!
# is_pareto_optimal

Topic: general_equilibrium   Node: c1486e194210

In a pure exchange economy E with finite agents Agent, an allocation x : Agent → Good → ℝ is Pareto optimal if x is feasible in E and there does not exist any feasible allocation y : Agent → Good → ℝ in E such that every agent i receives at least as high utility under y as under x (∀ i, E.utility i (x i) ≤ E.utility i (y i)) and at least one agent receives strictly higher utility under y than under x (∃ i, E.utility i (x i) < E.utility i (y i)).
-/

/-- In a pure exchange economy, an allocation is Pareto optimal (Pareto efficient) if it is feasible and there is no feasible allocation where every agent is at least as well off and at least one agent is strictly better off. -/
def is_pareto_optimal {Agent Good : Type*} [Fintype Agent]
    (E : ExchangeEconomy Agent Good) (x : Agent → Good → ℝ) : Prop := is_feasible_allocation E x ∧
  ¬ ∃ y : Agent → Good → ℝ, is_feasible_allocation E y ∧
    (∀ i, E.utility i (x i) ≤ E.utility i (y i)) ∧
    (∃ i, E.utility i (x i) < E.utility i (y i))
