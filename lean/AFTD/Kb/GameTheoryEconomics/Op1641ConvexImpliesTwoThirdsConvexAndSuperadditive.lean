import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsSuperadditive
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsConvexIsSuperadditive
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# op_1641_convex_implies_two_thirds_convex_and_superadditive

Topic: general_equilibrium   Node: 1cdc4acaf36d

Provenance: helper lemma. arXiv:2611.16207, Core nonemptiness for 2/3-convex games, Section 2

Every convex coalitional game with real characteristic function is both 2/3-convex and superadditive.
-/

/-- Every convex game satisfies both 2/3-convexity and superadditivity. -/
theorem op_1641_convex_implies_two_thirds_convex_and_superadditive {N : Type*} [DecidableEq N]
    (G : CoalitionalGame N ℝ) (hconv : G.IsConvex) :
    G.IsTwoThirdsConvex ∧ G.IsSuperadditive := by
  refine ⟨?_, CoalitionalGame.IsConvex.isSuperadditive G hconv⟩
  intro S₁ S₂ S₃ _ _ _
  exact Or.inl ⟨hconv S₁ S₂, hconv S₁ S₃⟩
