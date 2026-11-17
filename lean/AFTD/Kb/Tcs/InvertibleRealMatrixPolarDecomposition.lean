import AFTD.Prelude

/-!
# invertible_real_matrix_polar_decomposition

Topic: quantum   Node: 444a58d5cff0

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3; standard polar decomposition used in its proof.

Every invertible real 3 by 3 matrix is the product of an orthogonal matrix and a positive definite matrix.
-/

theorem invertible_real_matrix_polar_decomposition (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : L.det ≠ 0) : ∃ O P : Matrix (Fin 3) (Fin 3) ℝ, O.transpose * O = 1 ∧ P.PosDef ∧ L = O * P := by
  let _ : PartialOrder (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.instPartialOrder
  let _ : StarOrderedRing (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.instStarOrderedRing
  let _ : NonnegSpectrumClass ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.instNonnegSpectrumClass
  let S : Matrix (Fin 3) (Fin 3) ℝ := L.transpose * L
  have hS_semi : S.PosSemidef := by
    change (L.transpose * L).PosSemidef
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial L]
    exact Matrix.posSemidef_conjTranspose_mul_self L
  have hS_nonneg : 0 ≤ S := hS_semi.nonneg
  have hL_unit : IsUnit L := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hL
  have hS_unit : IsUnit S := ((Matrix.isUnit_transpose L).mpr hL_unit).mul hL_unit
  let P : Matrix (Fin 3) (Fin 3) ℝ := CFC.sqrt S
  have hP_nonneg : 0 ≤ P := CFC.sqrt_nonneg S
  have hP_semi : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP_nonneg
  have hP_unit : IsUnit P := (CFC.isUnit_sqrt_iff S hS_nonneg).mpr hS_unit
  have hP_posdef : P.PosDef := hP_semi.posDef_iff_isUnit.mpr hP_unit
  have hP_sq : P * P = L.transpose * L := by
    change P * P = S
    rw [← sq P]
    exact CFC.sq_sqrt S hS_nonneg
  have hP_symm : P.transpose = P := by
    have h_herm : P.conjTranspose = P := hP_semi.1
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial P]
    exact h_herm
  let O : Matrix (Fin 3) (Fin 3) ℝ := L * P⁻¹
  refine ⟨O, P, ?_, hP_posdef, ?_⟩
  · have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP_unit
    have hP_inv_symm : (P⁻¹).transpose = P⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hP_symm]
    change (L * P⁻¹).transpose * (L * P⁻¹) = 1
    rw [Matrix.transpose_mul, hP_inv_symm]
    have h1 : P⁻¹ * L.transpose * (L * P⁻¹) = P⁻¹ * (L.transpose * L) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [h1, ← hP_sq]
    have h2 : P⁻¹ * (P * P) * P⁻¹ = (P⁻¹ * P) * (P * P⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h2]
    rw [Matrix.nonsing_inv_mul P hdet, Matrix.mul_nonsing_inv P hdet, Matrix.mul_one]
  · have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP_unit
    change L = (L * P⁻¹) * P
    exact (Matrix.nonsing_inv_mul_cancel_right P L hdet).symm
