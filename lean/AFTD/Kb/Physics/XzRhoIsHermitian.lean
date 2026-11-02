import AFTD.Prelude
import AFTD.Kb.Physics.XzRho
import AFTD.Kb.Physics.XzMatrixA
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliMatrix

/-!
# xz_rho_is_hermitian

Topic: quantum_mechanics   Node: f6fa8b947816

Provenance: helper lemma. arXiv:2610.20846, Appendix C

For every natural number L, the reduced density matrix `xz_rho L` is Hermitian: `(xz_rho L).IsHermitian`.
-/

private lemma xz_rho_is_hermitian_pauli_basis_entry (b : PauliBasis) (i j : Fin 2) :
    star (b.toMatrix j i) = b.toMatrix i j := by
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]

private lemma xz_rho_is_hermitian_pauli_matrix {n : ℕ} (p : PauliString n) :
    (pauliMatrix p).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, pauliMatrix]
  rw [star_prod]
  exact Finset.prod_congr rfl fun x _ =>
    xz_rho_is_hermitian_pauli_basis_entry (p x) (i x) (j x)

private lemma xz_rho_is_hermitian_xz_matrix_a (L : ℕ) : (xz_matrix_a L).IsHermitian := by
  rw [xz_matrix_a]
  apply Matrix.IsHermitian.smul
  · rw [Matrix.isHermitian_iff_isSelfAdjoint]
    apply isSelfAdjoint_sum
    intro a _
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact xz_rho_is_hermitian_pauli_matrix _
  · rw [IsSelfAdjoint]
    simp

/-- The reduced density matrix rho_L is Hermitian for any length L. -/
theorem xz_rho_is_hermitian (L : ℕ) : (xz_rho L).IsHermitian := by
  rw [xz_rho, ← pow_two]
  exact (xz_rho_is_hermitian_xz_matrix_a L).pow 2
