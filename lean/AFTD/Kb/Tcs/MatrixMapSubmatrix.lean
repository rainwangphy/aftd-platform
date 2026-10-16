import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapMapChoiInv
import AFTD.Kb.Tcs.MatrixMapChoiMapInv

/-!
# MatrixMap.submatrix

Topic: quantum   Node: f3a8abec80aa

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.submatrix`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `MatrixMap` corresponding to applying a `submatrix` operation on each side.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable {A B : Type*} (R : Type*) [Semiring R] in
/-- The `MatrixMap` corresponding to applying a `submatrix` operation on each side. -/
@[simps]
def MatrixMap.submatrix (f : B → A) : MatrixMap A B R where
  toFun x := x.submatrix f f
  map_add' := by simp [Matrix.submatrix_add]
  map_smul' := by simp [Matrix.submatrix_smul]
