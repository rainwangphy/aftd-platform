import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalSelfAdjoint
import AFTD.Kb.Tcs.InstRCLikeIsMaximalSelfAdjoint
import AFTD.Kb.Tcs.IsMaximalSelfAdjointRCLikeSelfadjMap
import AFTD.Kb.Tcs.IsMaximalSelfAdjointTrivialSelfadjMap
import AFTD.Kb.Tcs.InstTrivialStarIsMaximalSelfAdjoint

/-!
# selfAdjointMap_Continuous

Topic: quantum   Node: 03abb2301868

Provenance: formalization of a published result. Source: QuantumInfo, `selfAdjointMap_Continuous`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/VonNeumann.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

selfAdjointMap_Continuous
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
@[fun_prop]
theorem selfAdjointMap_Continuous {𝕜 : Type*} [RCLike 𝕜] :
    Continuous (IsMaximalSelfAdjoint.selfadjMap : 𝕜 →+ ℝ) := by
  rw [IsMaximalSelfAdjoint.RCLike_selfadjMap]
  fun_prop
