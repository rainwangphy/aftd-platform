import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapChoiMatrix
import AFTD.Kb.Tcs.MatrixMapOfChoiMatrix
import AFTD.Kb.Tcs.MatrixMapChoiMapInv
import AFTD.Kb.Tcs.MatrixMapMapChoiInv

/-!
# MatrixMap.choi_matrix_inj

Topic: quantum   Node: 535e829c4cfd

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.choi_matrix_inj`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The correspondence induced by `MatrixMap.of_choi_matrix` is injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixMap in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
/-- The correspondence induced by `MatrixMap.of_choi_matrix` is injective. -/
theorem MatrixMap.choi_matrix_inj : Function.Injective (@choi_matrix A B R _ _) := by
  intro _ _ h
  simpa only [choi_map_inv] using congrArg of_choi_matrix h
