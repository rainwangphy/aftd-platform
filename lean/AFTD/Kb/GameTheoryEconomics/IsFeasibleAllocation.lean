import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy

/-!
# is_feasible_allocation

Topic: general_equilibrium   Node: c0c7d29ecf49

In a pure exchange economy E with finite agents Agent, an allocation x : Agent → Good → ℝ is feasible if every agent receives a non-negative consumption bundle (∀ i g, 0 ≤ x i g) and the total consumption of each good across all agents does not exceed the total endowment (∀ g, ∑ i, x i g ≤ ∑ i, E.endowment i g).
-/

/-- An allocation `x` is feasible in an exchange economy `E` if each bundle is non-negative and total consumption does not exceed total endowment. -/
def is_feasible_allocation {Agent Good : Type*} [Fintype Agent]
    (E : ExchangeEconomy Agent Good) (x : Agent → Good → ℝ) : Prop := (∀ i g, 0 ≤ x i g) ∧ (∀ g, ∑ i, x i g ≤ ∑ i, E.endowment i g)
