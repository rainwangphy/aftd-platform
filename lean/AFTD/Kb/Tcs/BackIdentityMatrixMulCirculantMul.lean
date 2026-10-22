import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.BackIdentityMatrixMulCirculant

/-!
# back_identity_matrix_mul_circulant_mul

Topic: combinatorics   Node: e99f795c5c7d

Provenance: helper lemma. helper for the Goethals-Seidel array identity, arXiv:2610.27175 Theorem 3

R (circulant v Z) = circulant(i ↦ v(-i)) (R Z): the back-identity moves rightward past a circulant, transposing it.
-/

theorem back_identity_matrix_mul_circulant_mul {m : ℕ} [NeZero m] (v : Fin m → ℤ)
    (Z : Matrix (Fin m) (Fin m) ℤ) :
    back_identity_matrix m * (Matrix.circulant v * Z)
      = Matrix.circulant (fun i => v (-i)) * (back_identity_matrix m * Z) := by
  rw [← Matrix.mul_assoc, back_identity_matrix_mul_circulant, Matrix.mul_assoc]
