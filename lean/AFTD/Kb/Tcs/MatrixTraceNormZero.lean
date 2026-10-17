import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceNorm

/-!
# Matrix.traceNorm_zero

Topic: quantum   Node: 6efcced8d80d

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm_zero`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.traceNorm_zero
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
@[simp]
theorem Matrix.traceNorm_zero : traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]
