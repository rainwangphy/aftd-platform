import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapMapChoiInv
import AFTD.Kb.Tcs.MatrixMapChoiMapInv

/-!
# MatrixMap.of_kraus

Topic: quantum   Node: b36947f4c23c

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.of_kraus`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Construct a matrix map out of families of matrices M N : Σ → Matrix B A R indexed by κ via X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Star R] [CommSemiring R] in
variable {κ : Type*} [Fintype κ] in
/-- Construct a matrix map out of families of matrices M N : Σ → Matrix B A R indexed by κ via X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ -/
def MatrixMap.of_kraus (M N : κ → Matrix B A R) : MatrixMap A B R :=
  ∑ k : κ, {
    toFun X := M k * X * (N k).conjTranspose
    map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  }
