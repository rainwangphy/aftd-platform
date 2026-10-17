import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixOpNorm

/-!
# Matrix.opNorm_mul_le

Topic: quantum   Node: d37f245d819d

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.opNorm_mul_le`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/SSA.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The operator norm of a matrix product is at most the product of the operator norms.
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
/-- The operator norm of a matrix product is at most the product of the operator norms. -/
theorem Matrix.opNorm_mul_le {l m n 𝕜 : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
  have h_comp : Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
    ext; simp [toEuclideanLin]
  simp only [Matrix.opNorm, h_comp]
  exact ContinuousLinearMap.opNorm_comp_le (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B))
