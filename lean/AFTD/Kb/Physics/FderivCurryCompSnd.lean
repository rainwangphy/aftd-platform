import AFTD.Prelude

/-!
# fderiv_curry_comp_snd

Topic: classical_mechanics   Node: 368ac5f2bee1

Provenance: formalization of a published result. Source: Physlib, `fderiv_curry_comp_snd`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_curry_comp_snd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_curry_comp_snd (f : X → Y → Z) (x : X) (y dy : Y)
    (hf : Differentiable 𝕜 (↿f)) :
    (fderiv 𝕜 (fun y' => f x y') y) dy
    =
    (fderiv 𝕜 (↿f) ((x, ·) y)) ((fderiv 𝕜 (x, ·) y) dy) := by
  have hl (x : X) : (fun y' => f x y') = ↿f ∘ (x, ·) := by
    rfl
  rw [hl]
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  · fun_prop
  · fun_prop
