import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsConvex.isTwoThirdsConvex

Topic: general_equilibrium   Node: 42dbc248e6e0

Provenance: helper lemma. arXiv:2611.16207, Core nonemptiness for 2/3-convex games, Section 2

Every convex coalitional game with real characteristic function is 2/3-convex.
-/

/-- Every convex coalitional game is 2/3-convex. -/
theorem CoalitionalGame.IsConvex.isTwoThirdsConvex {N : Type*} [DecidableEq N] (G : CoalitionalGame N ℝ)
    (hconv : G.IsConvex) : G.IsTwoThirdsConvex := by
  intro S₁ S₂ S₃ _ _ _
  exact Or.inl ⟨hconv S₁ S₂, hconv S₁ S₃⟩
