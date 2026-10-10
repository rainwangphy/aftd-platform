import AFTD.Prelude
import AFTD.Kb.Physics.FderivUncurryDifferentiableSndCompFstApply

/-!
# fderiv_curry_differentiableAt_snd_comp_fst

Topic: classical_mechanics   Node: 6c72a3ce86bc

Provenance: formalization of a published result. Source: Physlib, `fderiv_curry_differentiableAt_snd_comp_fst`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_curry_differentiableAt_snd_comp_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_curry_differentiableAt_snd_comp_fst (f : X → Y → Z) (x : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    DifferentiableAt 𝕜 (fun x' => (fderiv 𝕜 (fun y' => f x' y') y) dy) x := by
  apply Differentiable.differentiableAt
  fun_prop

/- fderiv commutes on X × Y. -/
