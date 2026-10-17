import AFTD.Prelude

/-!
# Matrix.IsHermitian.sum_eigenvalues_eq_trace

Topic: quantum   Node: eac0a9cd8ed9

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.IsHermitian.sum_eigenvalues_eq_trace`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The sum of the eigenvalues of a Hermitian matrix is equal to its trace.
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
/-- The sum of the eigenvalues of a Hermitian matrix is equal to its trace. -/
theorem Matrix.IsHermitian.sum_eigenvalues_eq_trace : ∑ i, hA.eigenvalues i = A.trace := by
  nth_rewrite 2 [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [trace_mul_comm, ← mul_assoc]
  simp [trace_diagonal]
