import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# is_pure_nash_equilibrium

Topic: equilibria   Node: 3fe03d4cfb1f

In a strategic-form game G with player type Player, a strategy profile s : ∀ i, G.Strategy i is a pure Nash equilibrium if for every player i : Player and every alternative strategy s_i' : G.Strategy i, player i's payoff from unilaterally deviating to s_i' satisfies G.payoff i (Function.update s i s_i') ≤ G.payoff i s.
-/

/-- Predicate asserting that a pure strategy profile is a Nash equilibrium. -/
def is_pure_nash_equilibrium {Player : Type*} [DecidableEq Player] (G : StrategicGame Player)
    (s : ∀ i, G.Strategy i) : Prop :=
  ∀ (i : Player) (s_i' : G.Strategy i), G.payoff i (Function.update s i s_i') ≤ G.payoff i s
