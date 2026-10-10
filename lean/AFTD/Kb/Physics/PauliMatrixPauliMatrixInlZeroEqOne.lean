import AFTD.Prelude
import AFTD.Kb.Physics.PauliMatrixPauliMatrix

/-!
# PauliMatrix.pauliMatrix_inl_zero_eq_one

Topic: special_relativity   Node: 27a554af6040

Provenance: formalization of a published result. Source: Physlib, `PauliMatrix.pauliMatrix_inl_zero_eq_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/PauliMatrices/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 adapted; compiled here.

PauliMatrix.pauliMatrix_inl_zero_eq_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open TensorProduct in
lemma PauliMatrix.pauliMatrix_inl_zero_eq_one : PauliMatrix.pauliMatrix (Sum.inl 0) = 1 := by
  dsimp [PauliMatrix.pauliMatrix]
