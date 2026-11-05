import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSteinNumber

/-!
# is_stein_number_five

Topic: combinatorial_games   Node: 5a12e65cf929

Provenance: formalization of a published result. Source: arXiv:2611.05898, Example 1.4

The integer 5 is an E. P. Stein number.
-/

/-- The number 5 is an E. P. Stein number. -/
theorem is_stein_number_five : is_stein_number 5 := by
  unfold is_stein_number
  norm_num
