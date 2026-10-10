import AFTD.Prelude
import AFTD.Kb.Physics.PauliMatrixPauliMatrix
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# PauliMatrix.trace_pauliMatrix_mul_pauliMatrix

Topic: special_relativity   Node: 82dd2e1414e4

Provenance: formalization of a published result. Source: Physlib, `PauliMatrix.trace_pauliMatrix_mul_pauliMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/PauliMatrices/SelfAdjoint.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Pauli matrices are orthogonal with respect to the trace pairing: `tr(σ_μ σ_ν) = 2 δ_μν`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Module KroneckerDelta in
open Complex in
/-- Pauli matrices are orthogonal with respect to the trace pairing: `tr(σ_μ σ_ν) = 2 δ_μν`. -/
@[simp]
lemma PauliMatrix.trace_pauliMatrix_mul_pauliMatrix (μ ν : Fin 1 ⊕ Fin 3) :
    Matrix.trace (PauliMatrix.pauliMatrix μ * PauliMatrix.pauliMatrix ν) = ((2 * kroneckerDelta μ ν : ℕ) : ℂ) := by
  fin_cases μ <;> fin_cases ν <;> simp [kroneckerDelta, PauliMatrix.pauliMatrix] <;> norm_num
