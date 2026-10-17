import AFTD.Prelude

/-!
# Equiv.Perm.permMatrix_mem_unitaryGroup

Topic: quantum   Node: 92173dfbe256

Provenance: formalization of a published result. Source: QuantumInfo, `Equiv.Perm.permMatrix_mem_unitaryGroup`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Isometry.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equiv.Perm.permMatrix_mem_unitaryGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Matrix in
variable {d d₂ d₃ R : Type*} in
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] in
variable [CommRing R] [StarRing R] in
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜} in
theorem Equiv.Perm.permMatrix_mem_unitaryGroup (e : Perm d) :
    e.permMatrix R ∈ Matrix.unitaryGroup d R := by
  -- Since $e$ is a permutation, its permutation matrix $P_e$ is orthogonal, meaning $P_e * P_e^T = I$.
  have h_perm_ortho : (Equiv.Perm.permMatrix R e) * (Equiv.Perm.permMatrix R e)ᵀ = 1 := by
    ext i j; rw [Matrix.mul_apply] ; aesop;
  constructor
  · simp_all only [Matrix.transpose_permMatrix]
    -- Since the conjugate transpose of a permutation matrix is the permutation matrix of the inverse permutation, we have:
    have h_conj_transpose : star (Equiv.Perm.permMatrix R e) = (Equiv.Perm.permMatrix R e)ᵀ := by
      ext i j; simp [Equiv.Perm.permMatrix] ; aesop;
    simp_all [mul_eq_one_comm]
  · simp_all only [Matrix.transpose_permMatrix]
    convert! h_perm_ortho using 2;
    simp [Matrix.star_eq_conjTranspose, Equiv.Perm.permMatrix]
