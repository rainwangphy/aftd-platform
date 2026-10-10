import AFTD.Prelude
import AFTD.Kb.Physics.FderivUncurryDifferentiableFstCompSndApply

/-!
# fderiv_curry_differentiableAt_fst_comp_snd

Topic: classical_mechanics   Node: 6b5dea1b54b8

Provenance: formalization of a published result. Source: Physlib, `fderiv_curry_differentiableAt_fst_comp_snd`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_curry_differentiableAt_fst_comp_snd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
@[fun_prop]
lemma fderiv_curry_differentiableAt_fst_comp_snd (f : X → Y → Z) (x dx : X) (y : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    DifferentiableAt 𝕜 (fun y' => (fderiv 𝕜 (fun x' => f x' y') x) dx) y := by
  apply Differentiable.differentiableAt
  fun_prop
