import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.IsPureNashEquilibrium

/-!
# pure_nash_of_subsingleton_strategy

Topic: equilibria   Node: 5ee569e07872

Provenance: original. Related work: machine-posed degenerate case of pure Nash equilibrium (singleton strategy sets); trivial, no novelty claimed

In a strategic game where every player has a subsingleton strategy set, every strategy profile is a pure Nash equilibrium.
-/

/-- In a game where every player has at most one strategy, any strategy profile is a pure Nash equilibrium. -/
theorem pure_nash_of_subsingleton_strategy {Player : Type*} [DecidableEq Player]
    (G : StrategicGame Player) [∀ i, Subsingleton (G.Strategy i)] (s : ∀ i, G.Strategy i) :
    is_pure_nash_equilibrium G s := by
  intro i s_i'
  rw [Subsingleton.elim (Function.update s i s_i') s]
