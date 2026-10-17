import AFTD.Prelude

/-!
# Matrix.unitaryGroup_row_norm

Topic: quantum   Node: 281f806d2d25

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.unitaryGroup_row_norm`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.unitaryGroup_row_norm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
theorem Matrix.unitaryGroup_row_norm [Fintype n] (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, ‖U j i‖^2 = 1 := by
  suffices ∑ j, ‖U j i‖^2 = (1 : ℂ) by exact_mod_cast this
  simpa [Matrix.mul_apply, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    using congr($(U.prop.left) i i)
