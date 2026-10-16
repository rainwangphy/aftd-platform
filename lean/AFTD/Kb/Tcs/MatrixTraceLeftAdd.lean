import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceLeft

/-!
# Matrix.traceLeft_add

Topic: quantum   Node: 5bdeac17e66a

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceLeft_add`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.traceLeft_add
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
theorem Matrix.traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft := by
  ext : 2
  simp [Matrix.traceLeft, Finset.sum_add_distrib]
