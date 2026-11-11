import AFTD.Prelude
import AFTD.Kb.Tcs.QaryMultipleDeletionHinge
import AFTD.Kb.Tcs.QaryAllZeroWord
import AFTD.Kb.Tcs.IsConstantWord
import AFTD.Kb.Tcs.DecidableIsConstantWord

/-!
# op_1534_ternary_length_two_one_deletion

Topic: information   Node: c556a9dfe650

Provenance: original. Related work: arXiv:2407.10026 "Conditional entropies of k-deletion/insertion channels"

For every ternary word y of length 2 (y : Fin 2 → Fin 3), the one-deletion hinge sums at thresholds r = 1 and r = 2 satisfy qary_multiple_deletion_hinge 1 3 2 1 y ≤ qary_multiple_deletion_hinge 1 3 2 1 (qary_all_zero_word 3 2 (by decide)) and qary_multiple_deletion_hinge 1 3 2 2 y ≤ qary_multiple_deletion_hinge 1 3 2 2 (qary_all_zero_word 3 2 (by decide)), with equality holding simultaneously at r = 1 and r = 2 if and only if y is constant (is_constant_word y).
-/

/-- OP-1534 holds for ternary alphabet of length 2 with 1 deletion. -/
theorem op_1534_ternary_length_two_one_deletion
    (y : Fin 2 → Fin 3) :
    qary_multiple_deletion_hinge 1 3 2 1 y ≤
      qary_multiple_deletion_hinge 1 3 2 1 (qary_all_zero_word 3 2 (by decide)) ∧
    qary_multiple_deletion_hinge 1 3 2 2 y ≤
      qary_multiple_deletion_hinge 1 3 2 2 (qary_all_zero_word 3 2 (by decide)) ∧
    ((qary_multiple_deletion_hinge 1 3 2 1 y =
        qary_multiple_deletion_hinge 1 3 2 1 (qary_all_zero_word 3 2 (by decide)) ∧
      qary_multiple_deletion_hinge 1 3 2 2 y =
        qary_multiple_deletion_hinge 1 3 2 2 (qary_all_zero_word 3 2 (by decide))) ↔
     is_constant_word y) := by
  revert y
  decide
