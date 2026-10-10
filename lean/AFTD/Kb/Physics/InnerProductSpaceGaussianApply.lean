import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpaceGaussian

/-!
# InnerProductSpace.gaussian_apply

Topic: classical_mechanics   Node: e7b5c000f680

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpace.gaussian_apply`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Gaussian.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

InnerProductSpace.gaussian_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
open ContinuousLinearMap Filter RCLike Real SchwartzMap in
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] in
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
variable (𝕜 : Type*) [RCLike 𝕜] in
variable (B : D ≃L[ℝ] E) (x₀ x : E) in
@[simp]
lemma InnerProductSpace.gaussian_apply : gaussian 𝕜 B x₀ x = ofReal (rexp (-2⁻¹ * ‖B.symm (x - x₀)‖ ^ 2)) := rfl
