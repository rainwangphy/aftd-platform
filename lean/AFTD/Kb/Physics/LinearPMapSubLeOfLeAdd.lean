import AFTD.Prelude

/-!
# LinearPMap.sub_le_of_le_add

Topic: classical_mechanics   Node: 3658f75a24a2

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sub_le_of_le_add`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sub_le_of_le_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.sub_le_of_le_add (h : g ≤ g₁ + g₂) : g - g₂ ≤ g₁ := by
  constructor
  · exact (inf_le_of_left_le le_rfl).trans (le_inf_iff.mp <| add_domain g₁ g₂ ▸ h.1).1
  · intro ⟨x, hx⟩ ⟨y, hy⟩ rfl
    simp [sub_apply, @h.2 ⟨x, hx.1⟩ ⟨x, ⟨hy, hx.2⟩⟩ rfl, add_apply]
