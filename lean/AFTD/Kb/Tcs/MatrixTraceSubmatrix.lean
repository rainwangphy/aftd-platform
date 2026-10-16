import AFTD.Prelude

/-!
# Matrix.trace_submatrix

Topic: quantum   Node: 84ba401d63a2

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.trace_submatrix`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.trace_submatrix
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable {α : Type*} [AddCommMonoid α] in
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] in
@[simp]
theorem Matrix.trace_submatrix
  (A : Matrix d₁ d₁ α) (e : d₂ ≃ d₁) :
    (A.submatrix e e).trace = A.trace := by
  simpa [Matrix.trace] using e.sum_comp (fun x ↦ A x x)
