import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixApply

/-!
# back_identity_matrix_mul_apply

Topic: combinatorics   Node: 81fc4a5b9b5e

Provenance: helper lemma. helper for bordered_goethals_seidel_is_hadamard (arXiv:2610.27175 Theorem 5)

Left multiplication by the back-identity matrix reverses the rows: (R X) i j = X (m - 1 - i) j.
-/

theorem back_identity_matrix_mul_apply {m : ℕ} (X : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    (back_identity_matrix m * X) i j = X i.rev j := by
  simp only [Matrix.mul_apply, back_identity_matrix_apply, ite_mul, one_mul, zero_mul]
  simp
