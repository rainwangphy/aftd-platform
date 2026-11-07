import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissibleInflectionSet
import AFTD.Kb.Tcs.PermInflectionSet

/-!
# op_686_two_three_three_four_admissible

Topic: combinatorics   Node: 283bd91b79b8

Provenance: helper lemma. arXiv:2610.38237, Section 3

The two-element set {(2, 3), (3, 4)} is an admissible inflection set (is_admissible_inflection_set {(2, 3), (3, 4)}).
-/

/-- The minimal two-element inflection set {(2, 3), (3, 4)} is admissible, witnessed by swap 2 3 in Sym 5. -/
theorem op_686_two_three_three_four_admissible :
    is_admissible_inflection_set {(2, 3), (3, 4)} := by
  use 5, Equiv.swap (2 : Fin 5) (3 : Fin 5)
  decide
