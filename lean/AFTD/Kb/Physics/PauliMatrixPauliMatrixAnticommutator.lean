import AFTD.Prelude
import AFTD.Kb.Physics.PauliMatrixPauliMatrix
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# PauliMatrix.pauliMatrix_anticommutator

Topic: special_relativity   Node: 8d5ceb453bd9

Provenance: formalization of a published result. Source: Physlib, `PauliMatrix.pauliMatrix_anticommutator`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/PauliMatrices/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Pauli matrices satisfy `{σᵢ, σⱼ} = 2 δᵢⱼ I`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open TensorProduct in
open KroneckerDelta in
/-- Pauli matrices satisfy `{σᵢ, σⱼ} = 2 δᵢⱼ I`. -/
lemma PauliMatrix.pauliMatrix_anticommutator (i j : Fin 3) :
    PauliMatrix.pauliMatrix (Sum.inr i) * PauliMatrix.pauliMatrix (Sum.inr j) +
      PauliMatrix.pauliMatrix (Sum.inr j) * PauliMatrix.pauliMatrix (Sum.inr i) =
        ((2 * kroneckerDelta i j : ℕ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [kroneckerDelta, PauliMatrix.pauliMatrix] <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num
