import AFTD.Prelude
import AFTD.Kb.Tcs.QaryTwoDeletionHinge
import AFTD.Kb.Tcs.IsSquarePathColoring

/-!
# op_1499_ternary_length_two

Topic: information   Node: c85284ad9cf2

Provenance: original. Related work: OP-1499; arXiv:2611.01064

For every ternary word y of length 2 (y : Fin 2 → Fin 3), the two-deletion hinge sums satisfy qary_two_deletion_hinge 3 2 2 y ≥ 2^2 + 2 - 1 and qary_two_deletion_hinge 3 2 3 y ≥ Nat.choose 2 2, and both equalities qary_two_deletion_hinge 3 2 2 y = 2^2 + 2 - 1 and qary_two_deletion_hinge 3 2 3 y = Nat.choose 2 2 hold simultaneously if and only if y is a proper coloring of the square of the path (is_square_path_coloring y).
-/

instance op_1499_ternary_length_two_dec (n q : ℕ) (y : Fin n → Fin q) :
    Decidable (is_square_path_coloring y) := by
  unfold is_square_path_coloring
  infer_instance

theorem op_1499_ternary_length_two_all : ∀ y : Fin 2 → Fin 3,
    qary_two_deletion_hinge 3 2 2 y ≥ 2^2 + 2 - 1 ∧
    qary_two_deletion_hinge 3 2 3 y ≥ Nat.choose 2 2 ∧
    ((qary_two_deletion_hinge 3 2 2 y = 2^2 + 2 - 1 ∧
      qary_two_deletion_hinge 3 2 3 y = Nat.choose 2 2) ↔
     is_square_path_coloring y) := by
  decide

/-- Verification of OP-1499 hinge majorization for all ternary words of length 2. -/
theorem op_1499_ternary_length_two
    (y : Fin 2 → Fin 3) :
    qary_two_deletion_hinge 3 2 2 y ≥ 2^2 + 2 - 1 ∧
    qary_two_deletion_hinge 3 2 3 y ≥ Nat.choose 2 2 ∧
    ((qary_two_deletion_hinge 3 2 2 y = 2^2 + 2 - 1 ∧
      qary_two_deletion_hinge 3 2 3 y = Nat.choose 2 2) ↔
     is_square_path_coloring y) := op_1499_ternary_length_two_all y
