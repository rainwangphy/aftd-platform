import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix

/-!
# pauli_bloch_matrix_square

Topic: quantum   Node: a8b895e527a2

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Eqs. (29)–(31), for the Pauli alignment construction.

The square of a Bloch Pauli matrix is the squared Euclidean length of its Bloch vector times the identity.
-/

theorem pauli_bloch_matrix_square (b : Fin 3 → ℝ) :
    pauli_bloch_matrix b * pauli_bloch_matrix b =
      ((∑ i, b i ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [pauli_bloch_matrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring
