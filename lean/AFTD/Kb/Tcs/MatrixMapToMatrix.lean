import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapMapChoiInv
import AFTD.Kb.Tcs.MatrixMapChoiMapInv
import AFTD.Kb.Tcs.MatrixMapChoiMatrix

/-!
# MatrixMap.toMatrix

Topic: quantum   Node: 9cd07dc203d3

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.toMatrix`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between MatrixMap's and transfer matrices on a larger space. Compare with `MatrixMap.choi_matrix`, which gives the Choi matrix instead of the transfer matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
variable {R : Type*} [CommSemiring R] in
/-- The linear equivalence between MatrixMap's and transfer matrices on a larger space. Compare with `MatrixMap.choi_matrix`, which gives the Choi matrix instead of the transfer matrix. -/
noncomputable def MatrixMap.toMatrix [Fintype B] : MatrixMap A B R ≃ₗ[R] Matrix (B × B) (A × A) R :=
  LinearMap.toMatrix (Matrix.stdBasis R A A) (Matrix.stdBasis R B B)
