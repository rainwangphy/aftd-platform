import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.IsPureNashEquilibrium

/-!
# not_pure_nash_of_exists_better_response

Topic: equilibria   Node: 9ee67a45d904

In a strategic-form game G, if some player i has an alternative strategy s_i' yielding a strictly higher payoff than at strategy profile s (that is, G.payoff i s < G.payoff i (Function.update s i s_i')), then s is not a pure Nash equilibrium.
-/

/-- A strategy profile is not a pure Nash equilibrium if some player has a strictly profitable unilateral deviation. -/
theorem not_pure_nash_of_exists_better_response {Player : Type*} [DecidableEq Player]
    (G : StrategicGame Player) (s : ∀ i, G.Strategy i)
    (i : Player) (s_i' : G.Strategy i)
    (h : G.payoff i s < G.payoff i (Function.update s i s_i')) :
    ¬ is_pure_nash_equilibrium G s := fun hnash => not_le_of_gt h (hnash i s_i')
