import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceLeft

/-!
# Matrix.IsHermitian.traceLeft

Topic: quantum   Node: 72383606f3b0

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.IsHermitian.traceLeft`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.IsHermitian.traceLeft
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable [AddCommMonoid R] [Fintype d] in
variable [StarAddMonoid R] in
theorem Matrix.IsHermitian.traceLeft {A : Matrix (d × d₁) (d × d₁) R} (hA : A.IsHermitian) : A.traceLeft.IsHermitian := by
  ext
  simp only [Matrix.traceLeft, conjTranspose_apply, of_apply, star_sum]
  congr!
  exact congrFun₂ hA _ _
