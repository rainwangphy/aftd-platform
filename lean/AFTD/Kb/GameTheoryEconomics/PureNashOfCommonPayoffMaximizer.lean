import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.IsPureNashEquilibrium

/-!
# pure_nash_of_common_payoff_maximizer

Topic: equilibria   Node: f6b42c801e48

In a strategic-form game G where all players have the same payoff function u (that is, G.payoff i s = u s for every player i and strategy profile s), any strategy profile s that globally maximizes u (that is, u s' ≤ u s for all strategy profiles s') is a pure Nash equilibrium.
-/

/-- In a common-payoff game, any strategy profile that globally maximizes the common payoff is a pure Nash equilibrium. -/
theorem pure_nash_of_common_payoff_maximizer {Player : Type*} [DecidableEq Player]
    (G : StrategicGame Player) (u : (∀ j, G.Strategy j) → ℝ)
    (h_common : ∀ (i : Player) (s : ∀ j, G.Strategy j), G.payoff i s = u s)
    (s : ∀ i, G.Strategy i)
    (h_max : ∀ s' : ∀ j, G.Strategy j, u s' ≤ u s) :
    is_pure_nash_equilibrium G s := by
  intro i s_i'
  rw [h_common, h_common]
  exact h_max (Function.update s i s_i')
