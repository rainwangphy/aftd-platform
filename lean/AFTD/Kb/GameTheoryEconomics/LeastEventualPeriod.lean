import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEventualPeriod

/-!
# least_eventual_period

Topic: combinatorial_games   Node: dc76867a6ae8

Provenance: formalization of a published result. Source: folklore

The least eventual period of a sequence $w : \mathbb{N} \to \text{Bool}$ is the infimum of the set of its positive eventual periods.
-/

/-- The least eventual period of a binary sequence is the infimum of its positive eventual periods. -/
noncomputable def least_eventual_period (w : ℕ → Bool) : ℕ := sInf {p : ℕ | is_eventual_period w p}
