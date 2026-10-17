import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry
import AFTD.Kb.Tcs.MatrixTraceNorm
import AFTD.Kb.Tcs.MatrixTraceNormZero
import AFTD.Kb.Tcs.MatrixTraceNormNeg

/-!
# Matrix.traceNorm_isometry_left

Topic: quantum   Node: 8eee6637340b

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm_isometry_left`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trace norm is invariant under left multiplication by an isometry.
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
open MatrixOrder Isometry in
/-- The trace norm is invariant under left multiplication by an isometry. -/
theorem Matrix.traceNorm_isometry_left [Fintype k] {A : Matrix n m R} {u : Matrix k n R}
  (hu₁ : u.Isometry) : traceNorm (u * A) = traceNorm A := by
  unfold traceNorm
  congr 1
  simp [Matrix.mul_assoc]
  nth_rw 2 [← Matrix.mul_assoc]
  simp [show uᴴ * u = 1 from hu₁]
