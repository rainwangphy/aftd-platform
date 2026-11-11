import AFTD.Prelude
import AFTD.Kb.Tcs.QaryTwoDeletionHinge
import AFTD.Kb.Tcs.IsSquarePathColoring

/-!
# op_1499_quaternary_length_two

Topic: information   Node: 71e8ded9d20c

Provenance: original. Related work: OP-1499; arXiv:2611.01064

For every quaternary word y of length 2 (y : Fin 2 → Fin 4), the two-deletion hinge sums satisfy qary_two_deletion_hinge 4 2 2 y ≥ 2^2 + 2 - 1 and qary_two_deletion_hinge 4 2 3 y ≥ Nat.choose 2 2, and both equalities qary_two_deletion_hinge 4 2 2 y = 2^2 + 2 - 1 and qary_two_deletion_hinge 4 2 3 y = Nat.choose 2 2 hold simultaneously if and only if y is a proper coloring of the square of the path (is_square_path_coloring y).
-/

/-- Verification of OP-1499 hinge majorization for all quaternary words of length 2. -/
theorem op_1499_quaternary_length_two
    (y : Fin 2 → Fin 4) :
    qary_two_deletion_hinge 4 2 2 y ≥ 2^2 + 2 - 1 ∧
    qary_two_deletion_hinge 4 2 3 y ≥ Nat.choose 2 2 ∧
    ((qary_two_deletion_hinge 4 2 2 y = 2^2 + 2 - 1 ∧
      qary_two_deletion_hinge 4 2 3 y = Nat.choose 2 2) ↔
     is_square_path_coloring y) := by
  simp only [is_square_path_coloring]
  decide +revert
