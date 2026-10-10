import AFTD.Prelude
import AFTD.Kb.Physics.GradientInnerSelf

/-!
# hasGradientAt_inner_self

Topic: classical_mechanics   Node: 478683a2ae47

Provenance: formalization of a published result. Source: Physlib, `hasGradientAt_inner_self`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of `y ↦ ⟪y, y⟫` is `2 • y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of `y ↦ ⟪y, y⟫` is `2 • y`. -/
lemma hasGradientAt_inner_self (x : F) : HasGradientAt (fun y : F => ⟪y, y⟫_ℝ) ((2 : ℝ) • x) x := by
  rw [← gradient_inner_self x]
  exact (differentiableAt_fun_id.inner ℝ differentiableAt_fun_id).hasGradientAt
