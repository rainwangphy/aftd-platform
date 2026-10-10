import AFTD.Prelude

/-!
# LinearPMap.le_iff_neg_le_neg

Topic: classical_mechanics   Node: 57aab8bae68c

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.le_iff_neg_le_neg`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.le_iff_neg_le_neg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F} in
lemma LinearPMap.le_iff_neg_le_neg : g₁ ≤ g₂ ↔ -g₁ ≤ -g₂ :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun _ _ h'' ↦ by simp [h' h'']⟩, fun ⟨h, _⟩ ↦ ⟨h, fun _ _ _ ↦ by aesop⟩⟩
