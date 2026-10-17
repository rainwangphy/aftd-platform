import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapToMatrix
import AFTD.Kb.Tcs.MatrixMapMapChoiInv
import AFTD.Kb.Tcs.MatrixMapChoiMapInv

/-!
# MatrixMap.toMatrix_comp

Topic: quantum   Node: 9c631edb4266

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.toMatrix_comp`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multiplication of transfer matrices, `MatrixMap.toMatrix`, is equivalent to composition of maps.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixMap in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
variable {R : Type*} [CommSemiring R] in
/-- Multiplication of transfer matrices, `MatrixMap.toMatrix`, is equivalent to composition of maps. -/
theorem MatrixMap.toMatrix_comp [Fintype B] [Fintype C] [DecidableEq B] (M₁ : MatrixMap A B R) (M₂ : MatrixMap B C R) : toMatrix (M₂ ∘ₗ M₁) = (toMatrix M₂) * (toMatrix M₁) :=
  LinearMap.toMatrix_comp _ _ _ M₂ M₁
