import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry

/-!
# Matrix.isometry_preserves_norm

Topic: quantum   Node: 340a42b3bdc8

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.isometry_preserves_norm`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/SSA.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.isometry_preserves_norm
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
theorem Matrix.isometry_preserves_norm (A : Matrix n m 𝕜) (hA : A.Isometry) (x : EuclideanSpace 𝕜 m) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  rw [ ← sq_eq_sq₀ ( by positivity ) ( by positivity ), Matrix.Isometry ] at *;
  simp [ EuclideanSpace.norm_eq]
  have h_inner : ∀ x y : EuclideanSpace 𝕜 m, inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x y := by
    intro x y
    have h_inner_eq : inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x (toEuclideanLin A.conjTranspose (toEuclideanLin A y)) := by
      simp [ Matrix.toEuclideanLin, inner ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, ];
      simp [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm_cycle]
    simp_all [ Matrix.toEuclideanLin, toLpLin];
  convert congr_arg Real.sqrt ( congr_arg ( fun z => ‖z‖ ) ( h_inner x x ) ) using 1;
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ];
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ]

/-
The operator norm of an isometry is 1 (assuming the domain is non-empty).
-/
