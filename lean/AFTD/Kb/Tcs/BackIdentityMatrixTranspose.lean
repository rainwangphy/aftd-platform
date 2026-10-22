import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixApply

/-!
# back_identity_matrix_transpose

Topic: combinatorics   Node: b0d84c3fb971

Provenance: helper lemma. sanity lemma for back_identity_matrix; serves arXiv:2610.27175 Theorem 5

The back-identity matrix is symmetric: Rᵀ = R.
-/

theorem back_identity_matrix_transpose (m : ℕ) :
    (back_identity_matrix m).transpose = back_identity_matrix m := by
  ext i j
  simp only [Matrix.transpose_apply, back_identity_matrix_apply]
  congr 1
  apply propext
  constructor <;> intro h <;> rw [h, Fin.rev_rev]
