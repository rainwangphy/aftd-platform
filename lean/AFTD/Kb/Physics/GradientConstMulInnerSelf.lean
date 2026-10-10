import AFTD.Prelude
import AFTD.Kb.Physics.GradientConstMul
import AFTD.Kb.Physics.GradientInnerSelf

/-!
# gradient_const_mul_inner_self

Topic: classical_mechanics   Node: 24e133931272

Provenance: formalization of a published result. Source: Physlib, `gradient_const_mul_inner_self`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of `y ↦ c * ⟪y, y⟫` at `x` is `(2 * c) • x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of `y ↦ c * ⟪y, y⟫` at `x` is `(2 * c) • x`. -/
lemma gradient_const_mul_inner_self (c : ℝ) (x : F) :
    gradient (fun y : F => c * ⟪y, y⟫_ℝ) x = (2 * c) • x := by
  rw [gradient_const_mul c (differentiableAt_fun_id.inner ℝ differentiableAt_fun_id),
    gradient_inner_self, smul_smul, mul_comm]
