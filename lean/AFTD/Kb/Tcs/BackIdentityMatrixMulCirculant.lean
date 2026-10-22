import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.CirculantMulBackIdentityMatrix

/-!
# back_identity_matrix_mul_circulant

Topic: combinatorics   Node: b22fd96cdf8e

Provenance: helper lemma. helper for the Goethals-Seidel array identity, arXiv:2610.27175 Theorem 3

R times the circulant with first column v equals the circulant of i ↦ v(-i) times R.
-/

theorem back_identity_matrix_mul_circulant {m : ℕ} [NeZero m] (v : Fin m → ℤ) :
    back_identity_matrix m * Matrix.circulant v
      = Matrix.circulant (fun i => v (-i)) * back_identity_matrix m := by
  rw [circulant_mul_back_identity_matrix, Matrix.transpose_circulant]
  simp
