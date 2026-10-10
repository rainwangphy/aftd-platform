import AFTD.Prelude
import AFTD.Kb.Physics.HasGradientAtConstMul

/-!
# gradient_const_mul

Topic: classical_mechanics   Node: 81c38e9a2811

Provenance: formalization of a published result. Source: Physlib, `gradient_const_mul`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of a constant multiple of a differentiable function is the constant multiple of the gradient.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of a constant multiple of a differentiable function is the constant multiple of the gradient. -/
lemma gradient_const_mul {f : F → ℝ} {x : F} (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  exact (hf.hasGradientAt.const_mul c).gradient
