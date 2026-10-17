import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixKroneckerMapConjTranspose

/-!
# Matrix.PosSemidef.PosSemidef_kronecker

Topic: quantum   Node: 539996f2bfe9

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.PosSemidef_kronecker`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.PosSemidef_kronecker
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Matrix.PosSemidef in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open Kronecker in
open scoped ComplexOrder in
variable {m n 𝕜 : Type*} in
variable [Fintype m] [Fintype n] in
variable [RCLike 𝕜] [dn : DecidableEq n] in
variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} in
variable (hA : A.PosSemidef) (hB : B.PosSemidef) in
include hA hB in
theorem Matrix.PosSemidef.PosSemidef_kronecker : (A ⊗ₖ B).PosSemidef := by
  open Classical in
  rw [hA.left.spectral_theorem, hB.left.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [mul_kronecker_mul, mul_kronecker_mul]
  rw [star_eq_conjTranspose, star_eq_conjTranspose]
  rw [← kroneckerMap_conjTranspose]
  rw [diagonal_kronecker_diagonal]
  apply mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  rintro ⟨i₁, i₂⟩
  convert mul_nonneg (hA.eigenvalues_nonneg i₁) (hB.eigenvalues_nonneg i₂)
  rw [RCLike.nonneg_iff]
  simp
