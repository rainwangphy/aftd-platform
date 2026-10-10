import AFTD.Prelude
import AFTD.Kb.Physics.HasGradientAtInnerLeft

/-!
# hasGradientAt_inner_right

Topic: classical_mechanics   Node: 589bd566def1

Provenance: formalization of a published result. Source: Physlib, `hasGradientAt_inner_right`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of `y ↦ ⟪y, a⟫` is `a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of `y ↦ ⟪y, a⟫` is `a`. -/
lemma hasGradientAt_inner_right (a x : F) : HasGradientAt (fun y : F => ⟪y, a⟫_ℝ) a x := by
  simp_rw [real_inner_comm a]
  exact hasGradientAt_inner_left a x
