import AFTD.Prelude

/-!
# PauliMatrix.pauliMatrix

Topic: special_relativity   Node: 5ad54c47be2a

Provenance: formalization of a published result. Source: Physlib, `PauliMatrix.pauliMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/PauliMatrices/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Pauli matrices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open TensorProduct in
/-- The Pauli matrices. -/
noncomputable def PauliMatrix.pauliMatrix : Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | Sum.inl 0 => 1
  | Sum.inr 0 => !![0, 1; 1, 0]
  | Sum.inr 1 => !![0, -I; I, 0]
  | Sum.inr 2 => !![1, 0; 0, -1]
