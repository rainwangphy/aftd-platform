import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionSpinorMatrix

/-!
# quaternion_spinor_unitary_scaled

Topic: quantum   Node: 02ff8579dce7

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion reference spinor construction.

The quaternion spinor matrix is unitary up to the squared quaternion norm.
-/

theorem quaternion_spinor_unitary_scaled (q : Fin 4 → ℝ) :
    (quaternion_spinor_matrix q) * (quaternion_spinor_matrix q).conjTranspose =
      (((∑ i, (q i)^2 : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternion_spinor_matrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fin.sum_univ_four, Complex.star_def,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring
