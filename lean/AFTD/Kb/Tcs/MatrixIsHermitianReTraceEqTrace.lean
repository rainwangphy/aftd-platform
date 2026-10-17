import AFTD.Prelude

/-!
# Matrix.IsHermitian.re_trace_eq_trace

Topic: quantum   Node: 1a8fffcea299

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.IsHermitian.re_trace_eq_trace`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.IsHermitian.re_trace_eq_trace
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Matrix.IsHermitian in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜} in
variable (hA : A.IsHermitian) (hB : B.IsHermitian) in
variable [Fintype n] in
include hA in
omit [DecidableEq n] in
@[simp]
theorem Matrix.IsHermitian.re_trace_eq_trace : RCLike.re (A.trace) = A.trace := by
  rw [trace, map_sum, RCLike.ofReal_sum, IsHermitian.coe_re_diag hA]
