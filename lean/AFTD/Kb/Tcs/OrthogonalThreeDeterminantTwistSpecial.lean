import AFTD.Prelude

/-!
# orthogonal_three_determinant_twist_special

Topic: quantum   Node: 2b3fdf9c8edf

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, determinant sign in the spinor lift.

The determinant of an orthogonal real 3 by 3 matrix is a sign, and multiplying the matrix by that sign yields a special orthogonal matrix.
-/

theorem orthogonal_three_determinant_twist_special (O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O.transpose * O = 1) : let δ := O.det; δ ^ 2 = 1 ∧ (δ • O).transpose * (δ • O) = 1 ∧ (δ • O).det = 1 := by
  dsimp only
  have hdet : O.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hO
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    simpa [pow_two] using h
  constructor
  · exact hdet
  · constructor
    · simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
      rw [hO, smul_smul, ← pow_two, hdet, one_smul]
    · rw [Matrix.det_smul]
      simp only [Fintype.card_fin]
      calc
        O.det ^ 3 * O.det = O.det ^ 4 := by ring
        _ = 1 := by rw [show (4 : Nat) = 2 + 2 by norm_num, pow_add, hdet, one_mul]
