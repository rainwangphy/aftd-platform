import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapSumApply

/-!
# LinearPMap.neg_compRestricted

Topic: classical_mechanics   Node: 3b3da753d984

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.neg_compRestricted`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.neg_compRestricted
-/

set_option quotPrecheck false
open LinearPMap
@[inherit_doc compRestricted]
local infixr:80 " ∘ᵣ " => compRestricted

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable {G : Type*} [AddCommGroup G] [Module R G] in
variable (g g₁ g₂ : F →ₗ.[R] G) (f f₁ f₂ : E →ₗ.[R] F) in
variable {v : F →ₗ.[R] G} {u : E →ₗ.[R] F} in
@[simp]
lemma LinearPMap.neg_compRestricted : (-g) ∘ᵣ f = -g ∘ᵣ f := rfl
