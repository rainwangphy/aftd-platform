import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpaceGaussian
import AFTD.Kb.Physics.InnerProductSpaceGaussianApply

/-!
# InnerProductSpace.gaussian₀

Topic: classical_mechanics   Node: 595855055bf8

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpace.gaussian₀`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Gaussian.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The (unnormalized) `𝕜`-valued Gaussian `exp (-2⁻¹ * ‖B⁻¹ x‖ ^ 2)` as a Schwartz map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
open ContinuousLinearMap Filter RCLike Real SchwartzMap in
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] in
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
variable (𝕜 : Type*) [RCLike 𝕜] in
variable (B : D ≃L[ℝ] E) (x₀ x : E) in
/-- The (unnormalized) `𝕜`-valued Gaussian `exp (-2⁻¹ * ‖B⁻¹ x‖ ^ 2)` as a Schwartz map. -/
noncomputable abbrev InnerProductSpace.gaussian₀ : 𝓢(E, 𝕜) := gaussian 𝕜 B 0
