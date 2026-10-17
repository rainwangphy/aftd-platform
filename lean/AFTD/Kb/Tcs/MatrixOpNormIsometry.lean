import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry
import AFTD.Kb.Tcs.MatrixOpNorm
import AFTD.Kb.Tcs.MatrixIsometryPreservesNorm

/-!
# Matrix.opNorm_isometry

Topic: quantum   Node: c08648e889a7

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.opNorm_isometry`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/SSA.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.opNorm_isometry
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
theorem Matrix.opNorm_isometry [Nonempty m] (A : Matrix n m 𝕜) (hA : A.Isometry) : Matrix.opNorm A = 1 := by
  have h_opNorm : ∀ x : EuclideanSpace 𝕜 m, ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
    convert Matrix.isometry_preserves_norm A hA;
  refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
  · exact ⟨ 0, fun c hc => hc.1 ⟩;
  · aesop;
  · exact ⟨ 1, ⟨zero_le_one, fun x => le_of_eq (by simp [h_opNorm])⟩ ⟩;
  · norm_num +zetaDelta at *;
    intro b hb h; specialize h ( EuclideanSpace.single ( Classical.arbitrary m ) 1 ) ; aesop;
