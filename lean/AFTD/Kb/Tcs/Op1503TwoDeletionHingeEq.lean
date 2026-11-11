import AFTD.Prelude
import AFTD.Kb.Tcs.QaryMultipleDeletionHinge
import AFTD.Kb.Tcs.QaryTwoDeletionHinge

/-!
# op_1503_two_deletion_hinge_eq

Topic: information   Node: 9561fe9d56bd

Provenance: helper lemma. knowledgebase, OP-1503

For any alphabet size q, length n, threshold r, and word y : Fin n → Fin q, the multiple-deletion hinge sum for two deletions qary_multiple_deletion_hinge 2 q n r y equals the two-deletion hinge sum qary_two_deletion_hinge q n r y.
-/

/-- Reduction of qary_multiple_deletion_hinge with 2 deletions to qary_two_deletion_hinge. -/
theorem op_1503_two_deletion_hinge_eq (q n r : ℕ) (y : Fin n → Fin q) :
    qary_multiple_deletion_hinge 2 q n r y = qary_two_deletion_hinge q n r y := by
  rfl
