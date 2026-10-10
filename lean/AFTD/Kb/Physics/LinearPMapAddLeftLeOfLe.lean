import AFTD.Prelude

/-!
# LinearPMap.add_left_le_of_le

Topic: classical_mechanics   Node: f4ad8cdde9e5

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.add_left_le_of_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.add_left_le_of_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.add_left_le_of_le (h : g₁ ≤ g₂) : f + g₁ ≤ f + g₂ := by
  constructor
  · simp only [add_domain, le_inf_iff, inf_le_left, true_and]
    exact (inf_le_of_right_le le_rfl).trans h.1
  · intro x y hxy
    simp_rw [add_apply, @h.2 ⟨x, x.2.2⟩ ⟨y, y.2.2⟩ hxy, hxy]
