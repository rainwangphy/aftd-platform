import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsThreeDistantConvex
import AFTD.Kb.Tcs.OrientedOverlapMultiplicityBudget

/-!
# zero_is_three_distant_convex

Topic: general_equilibrium   Node: 0867ccdf7ee1

Provenance: helper lemma. arXiv:2611.07572 Def 1

The zero game, where every coalition has value zero, is 3-distant convex.
-/

/-- The constant zero game is 3-distant convex. -/
theorem zero_is_three_distant_convex {α : Type*} [DecidableEq α] :
    is_three_distant_convex (fun (_ : Finset α) => (0 : ℝ)) := by first | exact oriented_overlap_multiplicity_budget | (apply oriented_overlap_multiplicity_budget <;> assumption) | (apply oriented_overlap_multiplicity_budget <;> simp_all) | simpa using oriented_overlap_multiplicity_budget | (simp only [is_three_distant_convex] at *; first | exact oriented_overlap_multiplicity_budget | (apply oriented_overlap_multiplicity_budget <;> assumption) | (apply oriented_overlap_multiplicity_budget <;> simp_all) | simpa using oriented_overlap_multiplicity_budget)
