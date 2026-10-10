import AFTD.Prelude

/-!
# gradient_inner_self

Topic: classical_mechanics   Node: d81d71a4fd6b

Provenance: formalization of a published result. Source: Physlib, `gradient_inner_self`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of `y ↦ ⟪y, y⟫` at `x` is `2 • x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of `y ↦ ⟪y, y⟫` at `x` is `2 • x`. -/
lemma gradient_inner_self (x : F) : gradient (fun y : F => ⟪y, y⟫_ℝ) x = (2 : ℝ) • x := by
  refine ext_inner_right (𝕜 := ℝ) fun y => ?_
  unfold gradient
  rw [toDual_symm_apply,
    fderiv_inner_apply (𝕜 := ℝ) differentiableAt_fun_id differentiableAt_fun_id]
  simp [real_inner_comm, inner_smul_right, two_mul]
