import AFTD.Prelude

/-!
# divergence

Topic: classical_mechanics   Node: 35a4b98190be

Provenance: formalization of a published result. Source: Physlib, `divergence`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Divergence.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The divergence of a map `f : E → E` where `E` is a normed space over `𝕜`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
variable (𝕜) in
/-- The divergence of a map `f : E → E` where `E` is a normed space over `𝕜`. -/
noncomputable def divergence (f : E → E) (x : E) : 𝕜 := (fderiv 𝕜 f x).toLinearMap.trace _ _
