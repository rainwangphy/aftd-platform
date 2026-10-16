import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap

/-!
# MatrixMap.of_choi_matrix

Topic: quantum   Node: bc47066b5d2f

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.of_choi_matrix`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given the Choi matrix, generate the corresponding R-linear map between matrices as a MatrixMap. This is the inverse of `MatrixMap.choi_matrix`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
set_option backward.isDefEq.respectTransparency false in
/-- Given the Choi matrix, generate the corresponding R-linear map between matrices as a MatrixMap. This is the inverse of `MatrixMap.choi_matrix`. -/
def MatrixMap.of_choi_matrix (M : Matrix (B × A) (B × A) R) : MatrixMap A B R where
  toFun X := fun b₁ b₂ ↦ ∑ (a₁ : A), ∑ (a₂ : A), X a₁ a₂ * M (b₁, a₁) (b₂, a₂)
  map_add' x y := by funext b₁ b₂; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b₁ b₂
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
