import AFTD.Prelude
import AFTD.Kb.Physics.FderivUncurryDifferentiableFstCompSnd

/-!
# fderiv_uncurry_differentiable_fst_comp_snd_apply

Topic: classical_mechanics   Node: 445edf566955

Provenance: formalization of a published result. Source: Physlib, `fderiv_uncurry_differentiable_fst_comp_snd_apply`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_uncurry_differentiable_fst_comp_snd_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
@[fun_prop]
lemma fderiv_uncurry_differentiable_fst_comp_snd_apply (f : X → Y → Z) (x δx : X)
    (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun y' => fderiv 𝕜 (fun x' => (↿f) (x', y')) x δx) := by
  fun_prop
