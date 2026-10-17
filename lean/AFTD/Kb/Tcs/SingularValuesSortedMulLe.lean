import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesSortedZeroEqSup
import AFTD.Kb.Tcs.QuadraticFormLeSingularValuesSortedSq
import AFTD.Kb.Tcs.SingularValuesSortedNonneg

/-!
# singularValuesSorted_mul_le

Topic: quantum   Node: 9c6dcb07d169

Provenance: formalization of a published result. Source: QuantumInfo, `singularValuesSorted_mul_le`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The largest singular value of a matrix product is at most the product of the largest singular values: `σ₁(M * N) ≤ σ₁(M) * σ₁(N)`. This is operator-norm submultiplicativity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The largest singular value of a matrix product is at most the product of the largest singular values: `σ₁(M * N) ≤ σ₁(M) * σ₁(N)`. This is operator-norm submultiplicativity. -/
lemma singularValuesSorted_mul_le {e : Type*} [Fintype e] [DecidableEq e]
    (M N : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted (M * N) ⟨0, h⟩ ≤
    singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
  rw [singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup]
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN).
  have h_eigenvalue_le : ∀ i, (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := by
    intro i
    have h_eigenvalue_le : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 := by
      -- By the properties of singular values and eigenvalues, we know that the eigenvalues of $(MN)^* (MN)$ are bounded by the product of the squares of the singular values of $M$ and $N$.
      have h_eigenvalue_bound : ∀ (v : e → ℂ), Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
        intro v
        have h_quadratic_form : Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) := by
          have := quadratic_form_le_singularValuesSorted_sq M h (N.mulVec v)
          convert this using 1 <;> simp [Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
        have h_quadratic_form_N : Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) ≤ (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
          convert quadratic_form_le_singularValuesSorted_sq N h v using 1
        simpa only [mul_assoc] using h_quadratic_form.trans (mul_le_mul_of_nonneg_left h_quadratic_form_N (sq_nonneg _))
      convert h_eigenvalue_bound ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvectorBasis i) using 1
      · have := (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues_eq i; aesop
      · simp [dotProduct]
        have := (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvectorBasis.orthonormal
        rw [orthonormal_iff_ite] at this
        simp_all [Complex.ext_iff, inner]
    linarith
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN) and take the square root.
  have h_sqrt_eigenvalue_le : ∀ i, singularValues (M * N) i ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
    intro i
    have h_sqrt_eigenvalue_le_i : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := h_eigenvalue_le i
    have h_sqrt_eigenvalue_le_i' : Real.sqrt ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i) ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (singularValuesSorted_nonneg M ⟨0, h⟩) (singularValuesSorted_nonneg N ⟨0, h⟩), h_sqrt_eigenvalue_le_i⟩
    exact h_sqrt_eigenvalue_le_i' |> le_trans (by
    exact le_rfl)
  simp_all [Finset.sup'_le_iff]
  convert h_sqrt_eigenvalue_le using 1
  rw [singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup]
