import AFTD.Prelude

/-!
# RCLike.instOrderClosed

Topic: quantum   Node: 638be5418de9

Provenance: formalization of a published result. Source: QuantumInfo, `RCLike.instOrderClosed`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Inner.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 adapted; compiled here.

RCLike.instOrderClosed
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {R n α : Type*} [Star R] [TrivialStar R] [Fintype n] in
open scoped InnerProductSpace RealInnerProductSpace in
variable {d d₂ : Type*} [Fintype d] [Fintype d₂] {𝕜 : Type*} [RCLike 𝕜] in
open ComplexOrder in
lemma RCLike.instOrderClosed : OrderClosedTopology 𝕜 where
  isClosed_le' := by
    conv => enter [1, 1, p]; rw [RCLike.le_iff_re_im]
    simp_rw [Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> continuity

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosed
