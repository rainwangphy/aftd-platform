import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.ZeroIsThreeDistantConvex

/-!
# zero_is_two_thirds_convex

Topic: general_equilibrium   Node: 5143975734af

Provenance: helper lemma. folklore

The constant zero game is 2/3-convex.
-/

/-- The zero game is 2/3-convex. -/
theorem zero_is_two_thirds_convex {α : Type*} [DecidableEq α] :
    is_two_thirds_convex (fun (_ : Finset α) => (0 : ℝ)) := by first | exact zero_is_three_distant_convex | (apply zero_is_three_distant_convex <;> assumption) | (apply zero_is_three_distant_convex <;> simp_all) | simpa using zero_is_three_distant_convex | (simp only [is_two_thirds_convex] at *; first | exact zero_is_three_distant_convex | (apply zero_is_three_distant_convex <;> assumption) | (apply zero_is_three_distant_convex <;> simp_all) | simpa using zero_is_three_distant_convex)
