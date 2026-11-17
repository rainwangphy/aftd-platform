import AFTD.Prelude

/-!
# invertible_pair_correlation_metric_factorization

Topic: quantum   Node: 65e4c09407ad

Provenance: helper lemma. arXiv:2611.19367v1, Section III D, Eqs. (35)–(37); the matrix factorization is stated for arbitrary finite dimension.

Given three real square matrices A, M and F with invertible determinants and a real scalar k, the three displayed invertible changes of coordinates simultaneously transform A, A M and k Fᵀ F M into the identity, identity and k times the identity.
-/

open Matrix

theorem invertible_pair_correlation_metric_factorization
    {n : Type*} [Fintype n] [DecidableEq n]
    (A M F : Matrix n n ℝ) (k : ℝ)
    (hA : IsUnit A.det) (hM : IsUnit M.det) (hF : IsUnit F.det) :
    let P := (A⁻¹).transpose * F.transpose
    let Q := F⁻¹
    let R := M⁻¹ * F⁻¹
    P.transpose * A * Q = 1 ∧
    P.transpose * (A * M) * R = 1 ∧
    Q.transpose * (k • (F.transpose * F * M)) * R = k • 1 := by
  dsimp
  have hAi := Matrix.nonsing_inv_mul A hA
  have hMi := Matrix.mul_nonsing_inv M hM
  have hFi := Matrix.mul_nonsing_inv F hF
  have hAleft (X : Matrix n n ℝ) : A⁻¹ * (A * X) = X := by
    rw [← Matrix.mul_assoc, hAi, Matrix.one_mul]
  have hMleft (X : Matrix n n ℝ) : M * (M⁻¹ * X) = X := by
    rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
  have hFit : (F⁻¹).transpose * F.transpose = 1 := by
    rw [← Matrix.transpose_mul, hFi, Matrix.transpose_one]
  constructor
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hAi,
      Matrix.one_mul, hFi]
  constructor
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hAleft,
      hMleft, hFi]
  · have hMM : M * (M⁻¹ * F⁻¹) = F⁻¹ := by
      rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc
      (F⁻¹).transpose * (F.transpose * F * M) * (M⁻¹ * F⁻¹) =
          ((F⁻¹).transpose * F.transpose) * (F * (M * (M⁻¹ * F⁻¹))) := by
            simp [Matrix.mul_assoc]
      _ = 1 := by rw [hFit, hMM, hFi]; simp
