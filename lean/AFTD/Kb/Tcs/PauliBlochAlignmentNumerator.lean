import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix
import AFTD.Kb.Tcs.PauliBlochMatrixSquare

/-!
# pauli_bloch_alignment_numerator

Topic: quantum   Node: d0f1e669c9eb

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Eqs. (29)–(31), for the Pauli alignment construction.

For two unit Bloch vectors b and t, set B and T to their Pauli matrices and N=I+TB. Then N†N=2(1+b·t)I and TN=NB.
-/

theorem pauli_bloch_alignment_numerator (b t : Fin 3 → ℝ)
    (hb : (∑ i, b i ^ 2) = 1) (ht : (∑ i, t i ^ 2) = 1) :
    let B := pauli_bloch_matrix b
    let T := pauli_bloch_matrix t
    let N := 1 + T * B
    N.conjTranspose * N = ((2 * (1 + ∑ i, b i * t i) : ℝ) : ℂ) • 1 ∧
    T * N = N * B := by
  dsimp
  have hB : pauli_bloch_matrix b * pauli_bloch_matrix b = 1 := by
    rw [pauli_bloch_matrix_square, hb]
    simp
  have hT : pauli_bloch_matrix t * pauli_bloch_matrix t = 1 := by
    rw [pauli_bloch_matrix_square, ht]
    simp
  constructor
  · simp only [Fin.sum_univ_three] at hb ht
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [pauli_bloch_matrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hb, ht]
  · calc
      pauli_bloch_matrix t * (1 + pauli_bloch_matrix t * pauli_bloch_matrix b) =
          pauli_bloch_matrix t + (pauli_bloch_matrix t * pauli_bloch_matrix t) * pauli_bloch_matrix b := by
            simp [Matrix.mul_add, Matrix.mul_assoc]
      _ = pauli_bloch_matrix t + pauli_bloch_matrix b := by rw [hT]; simp
      _ = pauli_bloch_matrix b + pauli_bloch_matrix t := add_comm _ _
      _ = (1 + pauli_bloch_matrix t * pauli_bloch_matrix b) * pauli_bloch_matrix b := by
            simp [Matrix.add_mul, Matrix.mul_assoc, hB]
