import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapLeIffNegLeNeg

/-!
# LinearPMap.le_neg_iff_neg_le

Topic: classical_mechanics   Node: bf416216dc88

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.le_neg_iff_neg_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.le_neg_iff_neg_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.le_neg_iff_neg_le : g₁ ≤ -g₂ ↔ -g₁ ≤ g₂ := by rw [le_iff_neg_le_neg, neg_neg]
