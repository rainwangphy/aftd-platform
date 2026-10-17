import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry
import AFTD.Kb.Tcs.MatrixTraceNorm
import AFTD.Kb.Tcs.MatrixTraceNormIsometryRight
import AFTD.Kb.Tcs.MatrixTraceNormIsometryLeft
import AFTD.Kb.Tcs.MatrixTraceNormZero
import AFTD.Kb.Tcs.MatrixTraceNormNeg

/-!
# Matrix.traceNorm_isometry_conj

Topic: quantum   Node: 78f403678f0c

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm_isometry_conj`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.traceNorm_isometry_conj
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
theorem Matrix.traceNorm_isometry_conj {A : Matrix n n R} {u : Matrix m n R}
  (hu : u.Isometry) {v : Matrix m n R} (hv : v.Isometry) :
    traceNorm (u * A * vᴴ) = traceNorm A := by
    rw [traceNorm_isometry_right hv, traceNorm_isometry_left hu]
