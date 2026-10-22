import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixMulSelf

/-!
# back_identity_matrix_mul_self_mul

Topic: combinatorics   Node: 5e4c7a10963a

Provenance: helper lemma. helper for the Goethals-Seidel array identity, arXiv:2610.27175 Theorem 3

R (R Z) = Z for the back-identity matrix R.
-/

theorem back_identity_matrix_mul_self_mul (m : ℕ) (Z : Matrix (Fin m) (Fin m) ℤ) :
    back_identity_matrix m * (back_identity_matrix m * Z) = Z := by
  rw [← Matrix.mul_assoc, back_identity_matrix_mul_self, Matrix.one_mul]
