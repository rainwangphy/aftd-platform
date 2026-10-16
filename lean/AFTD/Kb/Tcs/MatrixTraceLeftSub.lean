import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceLeft
import AFTD.Kb.Tcs.MatrixTraceLeftAdd
import AFTD.Kb.Tcs.MatrixTraceLeftNeg

/-!
# Matrix.traceLeft_sub

Topic: quantum   Node: 652764a1fdc5

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceLeft_sub`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.traceLeft_sub
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable {m α : Type*} [AddCommGroup α] [Fintype m] in
omit [DecidableEq n] in
variable {A B : Matrix (m × n) (m × n) α} in
@[simp]
theorem Matrix.traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft := by
  simp [sub_eq_add_neg]
