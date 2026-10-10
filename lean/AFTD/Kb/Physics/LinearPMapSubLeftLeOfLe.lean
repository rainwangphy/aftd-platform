import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapLeIffNegLeNeg
import AFTD.Kb.Physics.LinearPMapSubRightLeOfLe

/-!
# LinearPMap.sub_left_le_of_le

Topic: classical_mechanics   Node: 268b212ac8a9

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sub_left_le_of_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sub_left_le_of_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.sub_left_le_of_le (h : g₁ ≤ g₂) : f - g₁ ≤ f - g₂ :=
  neg_sub g₁ f ▸ neg_sub g₂ f ▸ le_iff_neg_le_neg.mp (sub_right_le_of_le f h)
