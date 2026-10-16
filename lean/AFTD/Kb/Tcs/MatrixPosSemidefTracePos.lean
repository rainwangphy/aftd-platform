import AFTD.Prelude

/-!
# Matrix.PosSemidef.trace_pos

Topic: quantum   Node: 8474df20b0e0

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.trace_pos`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.trace_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open ComplexOrder in
theorem Matrix.PosSemidef.trace_pos {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≠ 0) : 0 < A.trace := by
  apply hA.trace_nonneg.lt_of_ne'
  classical
  rw [hA.left.trace_eq_sum_eigenvalues]
  suffices ∑ i, hA.left.eigenvalues i ≠ 0 from mod_cast this
  rwa [ne_eq, Fintype.sum_eq_zero_iff_of_nonneg hA.eigenvalues_nonneg,
    hA.left.eigenvalues_eq_zero_iff]
