import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapInstMonoid

/-!
# LinearPMap.one_coe

Topic: classical_mechanics   Node: 579f01787e7a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.one_coe`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.one_coe
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
@[simp]
lemma LinearPMap.one_coe : (1 : E →ₗ.[R] E).toFun' = ⇑topEquiv.toLinearMap := rfl
