import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMapChoiMatrix
import AFTD.Kb.Tcs.MatrixMapOfChoiMatrix
import AFTD.Kb.Tcs.MatrixMapMapChoiInv
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapChoiMapInv

/-!
# MatrixMap.choi_equiv

Topic: quantum   Node: a123cbf9a7cf

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.choi_equiv`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between linear maps of matrices,and Choi matrices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixMap in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
variable {R : Type*} [CommSemiring R] in
/-- The linear equivalence between linear maps of matrices,and Choi matrices. -/
@[simps]
def MatrixMap.choi_equiv : MatrixMap A B R ≃ₗ[R] Matrix (B × A) (B × A) R where
  toFun := choi_matrix
  invFun := of_choi_matrix
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by ext; simp [choi_matrix]
  map_smul' _ _ := by ext; simp [choi_matrix]
