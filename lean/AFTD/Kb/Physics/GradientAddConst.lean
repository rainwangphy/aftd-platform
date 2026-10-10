import AFTD.Prelude

/-!
# gradient_add_const

Topic: classical_mechanics   Node: 040dbd6875b4

Provenance: formalization of a published result. Source: Physlib, `gradient_add_const`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Adding a constant to a function does not change its gradient.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- Adding a constant to a function does not change its gradient. -/
lemma gradient_add_const {f : F → ℝ} (c : ℝ) (x : F) :
    gradient (fun y => f y + c) x = gradient f x := by
  unfold gradient
  rw [fderiv_add_const]
