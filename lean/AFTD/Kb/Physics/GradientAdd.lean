import AFTD.Prelude
import AFTD.Kb.Physics.HasGradientAtAdd

/-!
# gradient_add

Topic: classical_mechanics   Node: 481519395f79

Provenance: formalization of a published result. Source: Physlib, `gradient_add`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of a sum of differentiable functions is the sum of their gradients.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of a sum of differentiable functions is the sum of their gradients. -/
lemma gradient_add {f g : F → ℝ} {x : F} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  exact (hf.hasGradientAt.add hg.hasGradientAt).gradient
