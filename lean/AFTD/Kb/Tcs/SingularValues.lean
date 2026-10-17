import AFTD.Prelude

/-!
# singularValues

Topic: quantum   Node: 48e2b0a386da

Provenance: formalization of a published result. Source: QuantumInfo, `singularValues`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The singular values of a square complex matrix `A`, defined as the square roots of the eigenvalues of `A†A`. These are indexed by `d` without a particular ordering. Note: We use `A.conjTranspose` as the argument to `isHermitian_mul_conjTranspose_self` so that the underlying Hermitian matrix is `A† * A` (matching the convention in `schattenNorm`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The singular values of a square complex matrix `A`, defined as the square roots of the eigenvalues of `A†A`. These are indexed by `d` without a particular ordering. Note: We use `A.conjTranspose` as the argument to `isHermitian_mul_conjTranspose_self` so that the underlying Hermitian matrix is `A† * A` (matching the convention in `schattenNorm`). -/
noncomputable def singularValues (A : Matrix d d ℂ) : d → ℝ :=
  fun i => Real.sqrt ((isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i)
