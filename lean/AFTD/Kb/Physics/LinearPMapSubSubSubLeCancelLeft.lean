import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapAddSubSubLeCancel

/-!
# LinearPMap.sub_sub_sub_le_cancel_left

Topic: classical_mechanics   Node: 596bda9b45d5

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sub_sub_sub_le_cancel_left`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sub_sub_sub_le_cancel_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.sub_sub_sub_le_cancel_left : f₁ - f₂ - (f₁ - f₃) ≤ f₃ - f₂ :=
  sub_eq_add_neg f₁ f₂ ▸ neg_add_eq_sub f₂ f₃ ▸ add_sub_sub_le_cancel f₁ (-f₂) f₃
