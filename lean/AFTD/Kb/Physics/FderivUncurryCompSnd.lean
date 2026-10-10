import AFTD.Prelude

/-!
# fderiv_uncurry_comp_snd

Topic: classical_mechanics   Node: 4f09e7551709

Provenance: formalization of a published result. Source: Physlib, `fderiv_uncurry_comp_snd`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_uncurry_comp_snd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_uncurry_comp_snd (f : X → Y → Z) (x : X) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 (fun y' => (↿f) (x, y'))
    =
    fun y => (fderiv 𝕜 (↿f) ((x, ·) y)).comp (fderiv 𝕜 (x, ·) y) := by
  have hl (x : X) : (fun y' => (↿f) (x, y')) = ↿f ∘ (x, ·) := by
    rfl
  rw [hl]
  funext y
  rw [fderiv_comp]
  · fun_prop
  · fun_prop
