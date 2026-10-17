import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceNorm
import AFTD.Kb.Tcs.MatrixTraceNormZero

/-!
# Matrix.traceNorm_neg

Topic: quantum   Node: 4d4078755432

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm_neg`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trace norm of the negative is equal to the trace norm.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
open Classical in
open scoped ComplexOrder in
variable {m n R : Type*} in
variable [Fintype m] [Fintype n] in
variable [RCLike R] in
/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem Matrix.traceNorm_neg (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _
