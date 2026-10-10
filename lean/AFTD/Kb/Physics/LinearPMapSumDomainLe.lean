import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapSum

/-!
# LinearPMap.sum_domain_le

Topic: classical_mechanics   Node: e94d00ae3213

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sum_domain_le`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sum_domain_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable {α : Type*} [Fintype α] (f : α → E →ₗ.[R] F) in
lemma LinearPMap.sum_domain_le (a : α) : (sum f).domain ≤ (f a).domain := fun _ _ ↦ by simp_all [sum, mem_iInf]
