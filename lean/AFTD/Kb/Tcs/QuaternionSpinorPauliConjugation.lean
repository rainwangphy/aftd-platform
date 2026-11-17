import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionSpinorMatrix
import AFTD.Kb.Tcs.QuaternionBlochRotation
import AFTD.Kb.Tcs.PauliBlochMatrix

/-!
# quaternion_spinor_pauli_conjugation

Topic: quantum   Node: f32ee7622b9f

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion reference spinor construction.

Quaternion spinor conjugation rotates a Pauli Bloch matrix by the associated real quaternion rotation.
-/

theorem quaternion_spinor_pauli_conjugation (q : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    quaternion_spinor_matrix q * pauli_bloch_matrix b * (quaternion_spinor_matrix q).conjTranspose =
      pauli_bloch_matrix ((quaternion_bloch_rotation q).mulVec b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternion_bloch_rotation, quaternion_spinor_matrix, pauli_bloch_matrix,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.cons_val_two, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring
