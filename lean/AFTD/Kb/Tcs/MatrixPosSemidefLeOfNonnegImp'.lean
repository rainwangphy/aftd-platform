import AFTD.Prelude

/-!
# Matrix.PosSemidef.le_of_nonneg_imp'

Topic: quantum   Node: 3da212c9a16f

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.le_of_nonneg_imp'`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.le_of_nonneg_imp'
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Matrix.PosSemidef in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open scoped ComplexOrder in
open scoped MatrixOrder in
variable {n m 𝕜 : Type*} in
variable [Fintype n] [Fintype m] [RCLike 𝕜] [DecidableEq m] in
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜} in
variable (hA : A.IsHermitian) (hB : B.IsHermitian) in
omit [Fintype n] in
theorem Matrix.PosSemidef.le_of_nonneg_imp' {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    {x y : R} (f : R →+ Matrix n n 𝕜) (h : ∀ x, 0 ≤ x → (f x).PosSemidef) :
    (x ≤ y → f x ≤ f y) := by
  intro hxy
  rw [← sub_nonneg, ← map_sub, Matrix.nonneg_iff_posSemidef]
  rw [← sub_nonneg] at hxy
  exact h (y - x) hxy
