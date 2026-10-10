import AFTD.Prelude

/-!
# fderiv_curry_comp_fst

Topic: classical_mechanics   Node: 175f032fd18b

Provenance: formalization of a published result. Source: Physlib, `fderiv_curry_comp_fst`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_curry_comp_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_curry_comp_fst (f : X → Y → Z) (x dx : X) (y : Y)
    (hf : Differentiable 𝕜 (↿f)) :
    (fderiv 𝕜 (fun x' => f x' y) x) dx
    =
    (fderiv 𝕜 (↿f) ((·, y) x)) ((fderiv 𝕜 (·, y) x) dx) := by
  have hl (y : Y) : (fun x' => f x' y) = ↿f ∘ (·, y) := by
    rfl
  rw [hl]
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  · fun_prop
  · fun_prop
