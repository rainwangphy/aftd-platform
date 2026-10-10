import AFTD.Prelude
import AFTD.Kb.Physics.FderivUncurry

/-!
# fderiv_curry_fst

Topic: classical_mechanics   Node: 5f4a3c956417

Provenance: formalization of a published result. Source: Physlib, `fderiv_curry_fst`. Lean proof by Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/FDerivCurry.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_curry_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] in
lemma fderiv_curry_fst (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x,y)) (dx : X) :
    fderiv 𝕜 (fun x' => Function.curry f x' y) x dx = fderiv 𝕜 f (x,y) (dx, 0) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  simp only [Function.curry_apply, map_zero, add_zero]
  exact h
