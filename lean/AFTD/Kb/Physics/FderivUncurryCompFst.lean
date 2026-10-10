import AFTD.Prelude

/-!
# fderiv_uncurry_comp_fst

Topic: classical_mechanics   Node: c52b6ce37d33

Provenance: formalization of a published result. Source: Physlib, `fderiv_uncurry_comp_fst`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_uncurry_comp_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_uncurry_comp_fst (f : X → Y → Z) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 (fun x' => (↿f) (x', y))
    =
    fun x => (fderiv 𝕜 (↿f) ((·, y) x)).comp (fderiv 𝕜 (·, y) x) := by
  have hl (y : Y) : (fun x' => (↿f) (x', y)) = ↿f ∘ (·, y) := by
    rfl
  rw [hl]
  funext x
  rw [fderiv_comp]
  · fun_prop
  · fun_prop
