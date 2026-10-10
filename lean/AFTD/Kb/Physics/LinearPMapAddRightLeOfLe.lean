import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapAddLeftLeOfLe

/-!
# LinearPMap.add_right_le_of_le

Topic: classical_mechanics   Node: 0940ca570d3f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.add_right_le_of_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.add_right_le_of_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.add_right_le_of_le (h : g₁ ≤ g₂) : g₁ + f ≤ g₂ + f :=
  add_comm f g₁ ▸ add_comm f g₂ ▸ add_left_le_of_le f h
