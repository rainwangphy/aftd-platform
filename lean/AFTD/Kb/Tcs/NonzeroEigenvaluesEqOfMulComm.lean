import AFTD.Prelude

/-!
# nonzero_eigenvalues_eq_of_mul_comm

Topic: quantum   Node: 7bfc65051776

Provenance: formalization of a published result. Source: QuantumInfo, `nonzero_eigenvalues_eq_of_mul_comm`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/VonNeumann.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The non-zero eigenvalues of AB and BA are the same.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace in
/-- The non-zero eigenvalues of AB and BA are the same. -/
lemma nonzero_eigenvalues_eq_of_mul_comm {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    (A * B).charpoly.roots.filter (· ≠ 0) = (B * A).charpoly.roots.filter (· ≠ 0) := by
  have h_roots : (Polynomial.X ^ Fintype.card m * (Matrix.charpoly (A * B))).roots.filter (· ≠ 0) = (Polynomial.X ^ Fintype.card n * (Matrix.charpoly (B * A))).roots.filter (· ≠ 0) := by
    rw [A.charpoly_mul_comm' B]
  convert h_roots using 1
  · simp [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero]
  · simp [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero]
