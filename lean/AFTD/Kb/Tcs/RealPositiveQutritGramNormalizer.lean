import AFTD.Prelude

/-!
# real_positive_qutrit_gram_normalizer

Topic: quantum   Node: b3ac3db2f03c

Provenance: helper lemma. Local compatibility helper for OP-693.

A positive-definite real qutrit Gram block has an invertible symmetric normalizing filter.
-/

open Matrix
open scoped BigOperators Matrix MatrixOrder ComplexOrder
set_option backward.isDefEq.respectTransparency false
private lemma in767_posnormalproof_real_positive_normalizer
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) :
    ∃ H : Matrix (Fin 3) (Fin 3) ℝ, H.transpose = H ∧ IsUnit H ∧ H*A*H=1 := by
  let S : Matrix (Fin 3) (Fin 3) ℝ := CFC.sqrt A
  have hSpos : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSsym : S.transpose=S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hSpos.isHermitian.eq
  have hSq : S*S=A := by
    have h := CFC.sq_sqrt A hA.posSemidef.nonneg
    simpa only [pow_two] using h
  have hSunit : IsUnit S := isUnit_of_mul_isUnit_left (hSq ▸ hA.isUnit)
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  let H : Matrix (Fin 3) (Fin 3) ℝ := S⁻¹
  have hHunit : IsUnit H := Matrix.isUnit_nonsing_inv_iff.mpr hSunit
  have hHsym : H.transpose=H := by
    have h := hSpos.isHermitian.inv
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h.eq
  have hHS : H*S=1 := Matrix.nonsing_inv_mul S hSdet
  have hSH : S*H=1 := Matrix.mul_nonsing_inv S hSdet
  refine ⟨H, hHsym, hHunit, ?_⟩
  calc
    H*A*H = H*(S*S)*H := by rw [hSq]
    _ = (H*S)*(S*H) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hHS,hSH,Matrix.one_mul]

theorem real_positive_qutrit_gram_normalizer :
  ∀ A : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef →
    ∃ H : Matrix (Fin 3) (Fin 3) ℝ,
      H.transpose = H ∧ IsUnit H ∧ H*A*H = 1 := by
  intro A hA
  exact in767_posnormalproof_real_positive_normalizer A hA
