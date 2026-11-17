import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix

/-!
# pauli_bloch_matrix_hermitian

Topic: quantum   Node: 053827896f3e

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Pauli alignment construction.

The Pauli matrix of a real Bloch vector is Hermitian.
-/

theorem pauli_bloch_matrix_hermitian (b : Fin 3 → ℝ) :
    (pauli_bloch_matrix b).conjTranspose = pauli_bloch_matrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli_bloch_matrix, Matrix.conjTranspose_apply, sub_eq_add_neg]
