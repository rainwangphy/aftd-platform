import AFTD.Prelude

/-!
# Matrix.unitary_col_sum_norm_sq

Topic: quantum   Node: 298738a4cead

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.unitary_col_sum_norm_sq`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Unitary.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a unitary matrix C, the column sums of ‖C i j‖^2 equal 1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α] in
variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- For a unitary matrix C, the column sums of ‖C i j‖^2 equal 1. -/
lemma Matrix.unitary_col_sum_norm_sq (C : Matrix d d ℂ) (hC : C.conjTranspose * C = 1) (j : d) :
    ∑ i, ‖C i j‖ ^ 2 = 1 := by
  replace hC := congr($hC j j)
  simp_rw [Matrix.mul_apply, mul_comm] at hC
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply_eq,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow] at hC
  exact_mod_cast hC
