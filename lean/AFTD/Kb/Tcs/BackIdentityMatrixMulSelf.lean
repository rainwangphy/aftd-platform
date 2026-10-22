import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixApply
import AFTD.Kb.Tcs.BackIdentityMatrixMulApply

/-!
# back_identity_matrix_mul_self

Topic: combinatorics   Node: 05617069448a

Provenance: helper lemma. sanity lemma for back_identity_matrix; serves arXiv:2610.27175 Theorem 5

The back-identity matrix is an involution: R R = I.
-/

theorem back_identity_matrix_mul_self (m : ℕ) :
    back_identity_matrix m * back_identity_matrix m = 1 := by
  ext i j
  rw [back_identity_matrix_mul_apply, back_identity_matrix_apply, Matrix.one_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [h, Fin.rev_rev]
  · intro h; rw [h, Fin.rev_rev]
