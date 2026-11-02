import AFTD.Prelude
import AFTD.Kb.Physics.XzMatrixA
import AFTD.Kb.Physics.XzPauliString
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ

/-!
# xz_matrix_a_is_hermitian

Topic: quantum_mechanics   Node: ce5cf0f2c6e9

Provenance: helper lemma. arXiv:2610.20846, Appendix C

For every natural number L, the matrix `xz_matrix_a L` is Hermitian: `(xz_matrix_a L).IsHermitian`.
-/

lemma xz_matrix_a_is_hermitian_pauli_basis (b : PauliBasis) : (b.toMatrix).IsHermitian := by
  cases b <;> {
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ, Matrix.conjTranspose]
  }

lemma xz_matrix_a_is_hermitian_pauli_matrix {n : ℕ} (p : PauliString n) : (pauliMatrix p).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  dsimp [pauliMatrix]
  change star (∏ k, (p k).toMatrix (j k) (i k)) = ∏ k, (p k).toMatrix (i k) (j k)
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro k _
  have h := xz_matrix_a_is_hermitian_pauli_basis (p k)
  have h_app := congr_fun (congr_fun h (i k)) (j k)
  rw [Matrix.conjTranspose_apply] at h_app
  exact h_app

/-- The matrix A_L is Hermitian for any length L. -/
theorem xz_matrix_a_is_hermitian (L : ℕ) : (xz_matrix_a L).IsHermitian := by
  unfold xz_matrix_a Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hstar : star (1 / (2 ^ L : ℂ)) = 1 / (2 ^ L : ℂ) := by simp
  rw [hstar]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact xz_matrix_a_is_hermitian_pauli_matrix (xz_pauli_string L a)
