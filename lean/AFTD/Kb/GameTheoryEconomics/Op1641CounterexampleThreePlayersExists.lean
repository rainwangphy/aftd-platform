import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsSuperadditive
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameShapleyValue
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCore
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.Op1641TwoThirdsConvexShapleyInCoreNegation
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector

/-!
# op_1641_counterexample_three_players_exists

Topic: general_equilibrium   Node: 3b0a1b559caf

Provenance: original. Related work: arXiv:2611.16207, Core nonemptiness for 2/3-convex games, Section 5

There exists a superadditive 2/3-convex coalitional game on 3 players whose Shapley value does not belong to its core.
-/

/-- Existence of a 3-player superadditive 2/3-convex game whose Shapley value is outside the core. -/
theorem op_1641_counterexample_three_players_exists :
    ∃ (G : CoalitionalGame (Fin 3) ℝ), G.IsSuperadditive ∧ G.IsTwoThirdsConvex ∧ G.shapleyValue ∉ G.Core := by
  exact ⟨op_1641_G, op_1641_G_superadd, op_1641_G_two_thirds_convex, op_1641_G_not_in_core⟩
