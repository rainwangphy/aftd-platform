import AFTD.Prelude
import AFTD.Kb.Physics.Divergence
import AFTD.Kb.Physics.DivergenceZero

/-!
# divergence_sub

Topic: classical_mechanics   Node: fdd414c82f97

Provenance: formalization of a published result. Source: Physlib, `divergence_sub`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Divergence.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

divergence_sub
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
lemma divergence_sub {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x - g x) x
    =
    divergence 𝕜 f x - divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_fun_sub hf hg]
