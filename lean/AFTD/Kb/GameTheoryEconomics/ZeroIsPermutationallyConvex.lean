import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPermutationallyConvex

/-!
# zero_is_permutationally_convex

Topic: general_equilibrium   Node: 6b5ff115545d

Provenance: helper lemma. folklore

The constant zero cooperative game is permutationally convex.
-/

/-- The constant zero game is permutationally convex. -/
theorem zero_is_permutationally_convex {α : Type*} [DecidableEq α] [Fintype α] :
    is_permutationally_convex (fun (_ : Finset α) => (0 : ℝ)) := by
  unfold is_permutationally_convex
  use (Fintype.equivFin α).symm
  intros
  norm_num
