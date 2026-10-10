import AFTD.Prelude

/-!
# function_differentiableAt_snd

Topic: classical_mechanics   Node: 3239a353c528

Provenance: formalization of a published result. Source: Physlib, `function_differentiableAt_snd`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

function_differentiableAt_snd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma function_differentiableAt_snd (f : X → Y → Z) (x : X) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    DifferentiableAt 𝕜 (fun y' => f x y') y := by
  have hl : (fun y' => f x y') = ↿f ∘ (x, ·) := by
    funext y'
    rfl
  rw [hl]
  apply Differentiable.differentiableAt
  apply Differentiable.comp <;> fun_prop
