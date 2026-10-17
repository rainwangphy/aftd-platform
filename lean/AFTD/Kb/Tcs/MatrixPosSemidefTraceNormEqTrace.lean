import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceNorm
import AFTD.Kb.Tcs.MatrixIsHermitianReTraceEqTrace
import AFTD.Kb.Tcs.MatrixIsometry
import AFTD.Kb.Tcs.MatrixTraceNormZero
import AFTD.Kb.Tcs.MatrixTraceNormNeg
import AFTD.Kb.Tcs.MatrixTraceNormUnitaryConj

/-!
# Matrix.PosSemidef.traceNorm_eq_trace

Topic: quantum   Node: f918a2129691

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.traceNorm_eq_trace`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A positive semidefinite matrix has trace norm equal to its trace.
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
/-- A positive semidefinite matrix has trace norm equal to its trace. -/
theorem Matrix.PosSemidef.traceNorm_eq_trace {A : Matrix m m R} (hA : A.PosSemidef) :
    A.traceNorm = A.trace := by
  have : Aᴴ * A = A^2 := by rw [hA.1, pow_two]
  open MatrixOrder in
  rw [traceNorm, this, CFC.sqrt_sq A, hA.1.re_trace_eq_trace]
