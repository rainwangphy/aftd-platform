import AFTD.Prelude

/-!
# Matrix.kronecker_conj_eq

Topic: quantum   Node: 2519173ef93d

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.kronecker_conj_eq`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conjugate of a Kronecker product by a Kronecker product is the Kronecker product of the conjugates (for matrices).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open scoped Matrix Kronecker in
/-- The conjugate of a Kronecker product by a Kronecker product is the Kronecker product of the conjugates (for matrices). -/
lemma Matrix.kronecker_conj_eq {m n p q α : Type*} [CommSemiring α] [StarRing α] [Fintype m] [Fintype n]
    (A : Matrix m m α) (B : Matrix n n α) (C : Matrix p m α) (D : Matrix q n α) :
    (C ⊗ₖ D) * (A ⊗ₖ B) * (C ⊗ₖ D)ᴴ = (C * A * Cᴴ) ⊗ₖ (D * B * Dᴴ) := by
  rw [← Matrix.mul_kronecker_mul]
  ext1
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, star_mul']
  simp only [← starRingEnd_apply, mul_comm, Finset.mul_sum, mul_left_comm]
  simp only [Finset.sum_mul, mul_assoc, Finset.mul_sum, mul_left_comm]
  rw [Fintype.sum_prod_type_right]
