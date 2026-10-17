import AFTD.Prelude
import AFTD.Kb.Tcs.IsometryMulConjTransposeLeOne
import AFTD.Kb.Tcs.MatrixPosSemidefMulMulConjTransposeMono

/-!
# conjTranspose_isometry_mul_isometry_le_one

Topic: quantum   Node: 4d651b348937

Provenance: formalization of a published result. Source: QuantumInfo, `conjTranspose_isometry_mul_isometry_le_one`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/SSA.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

conjTranspose_isometry_mul_isometry_le_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ m n : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix in
open scoped MatrixOrder ComplexOrder in
open scoped MatrixOrder in
variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] in
theorem conjTranspose_isometry_mul_isometry_le_one {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix k m ℂ) (B : Matrix k n ℂ)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A.conjTranspose * B).conjTranspose * (A.conjTranspose * B) ≤ 1 := by
  have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ 1 := by
    have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ (Bᴴ * B) := by
      have h_le : (A * Aᴴ) ≤ 1 := by
        apply isometry_mul_conjTranspose_le_one A hA;
      -- Apply the fact that if $X \leq Y$, then $CXC^* \leq CYC^*$ for any matrix $C$.
      have h_conj : ∀ (C : Matrix n k ℂ) (X Y : Matrix k k ℂ), X ≤ Y → C * X * Cᴴ ≤ C * Y * Cᴴ :=
        fun C X Y a => Matrix.PosSemidef.mul_mul_conjTranspose_mono C a
      simpa [ Matrix.mul_assoc ] using h_conj Bᴴ ( A * Aᴴ ) 1 h_le;
    aesop;
  simpa [ Matrix.mul_assoc ] using h_le
