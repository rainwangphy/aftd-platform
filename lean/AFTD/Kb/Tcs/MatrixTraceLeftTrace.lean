import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceLeft

/-!
# Matrix.traceLeft_trace

Topic: quantum   Node: 8ae7c885a927

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceLeft_trace`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.traceLeft_trace
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable [AddCommMonoid R] [Fintype d] in
variable [Fintype d₁] [Fintype d₂] in
@[simp]
theorem Matrix.traceLeft_trace (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceLeft.trace = A.trace := by
  convert! (Fintype.sum_prod_type_right _).symm
  rfl
