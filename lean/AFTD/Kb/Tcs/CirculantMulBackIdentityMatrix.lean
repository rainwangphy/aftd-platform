import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.MulBackIdentityMatrixApply
import AFTD.Kb.Tcs.BackIdentityMatrixMulApply
import AFTD.Kb.Tcs.FinSubRevComm

/-!
# circulant_mul_back_identity_matrix

Topic: combinatorics   Node: e0cea8f52da8

Provenance: helper lemma. arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), proof of Theorem 3 and Theorem 5: the relation X R = R Xᵀ for circulants

For a circulant integer matrix X of order m > 0 and the back-identity matrix R, X R = R Xᵀ.
-/

theorem circulant_mul_back_identity_matrix {m : ℕ} [NeZero m] (v : Fin m → ℤ) :
    Matrix.circulant v * back_identity_matrix m
      = back_identity_matrix m * (Matrix.circulant v).transpose := by
  ext i j
  rw [mul_back_identity_matrix_apply, back_identity_matrix_mul_apply, Matrix.transpose_apply,
    Matrix.circulant_apply, Matrix.circulant_apply, fin_sub_rev_comm]
