import AFTD.Prelude
import AFTD.Kb.Physics.Divergence

/-!
# divergence_zero

Topic: classical_mechanics   Node: 116f3f7b5586

Provenance: formalization of a published result. Source: Physlib, `divergence_zero`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Divergence.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

divergence_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
@[simp]
lemma divergence_zero : divergence 𝕜 (fun _ : E => 0) = fun _ => 0 := by
  unfold divergence
  simp
