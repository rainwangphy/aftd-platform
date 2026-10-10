import AFTD.Prelude
import AFTD.Kb.Physics.PauliMatrixPauliMatrix

/-!
# PauliMatrix.vectorMatrix

Topic: special_relativity   Node: 3279b22dfc33

Provenance: formalization of a published result. Source: Physlib, `PauliMatrix.vectorMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/PauliMatrices/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The matrix `a · σ` associated to a real three-vector `a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open TensorProduct in
/-- The matrix `a · σ` associated to a real three-vector `a`. -/
noncomputable def PauliMatrix.vectorMatrix (a : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 3, (a i : ℂ) • PauliMatrix.pauliMatrix (Sum.inr i)
