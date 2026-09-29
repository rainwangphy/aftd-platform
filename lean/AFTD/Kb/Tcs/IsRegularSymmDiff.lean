import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularDiff

/-!
# is_regular_symm_diff

Topic: automata   Node: b692e33f65aa

The symmetric difference of two regular languages is regular.
-/

/-- The symmetric difference of two regular languages is regular. -/
theorem is_regular_symm_diff {α : Type*} {L1 L2 : Language α} (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (symmDiff L1 L2).IsRegular := by
  rw [symmDiff_def]
  exact (is_regular_diff h1 h2).add (is_regular_diff h2 h1)
