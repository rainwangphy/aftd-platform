import AFTD.Prelude

/-!
# LinearPMap.sum

Topic: classical_mechanics   Node: f3e71f032b1f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sum`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite sum of partial linear maps. `sum f` and `∑ a, f a` are equal, but not by definition. With `sum f` both `domain` and `toFun` are made explicit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable {α : Type*} [Fintype α] (f : α → E →ₗ.[R] F) in
/-- A finite sum of partial linear maps. `sum f` and `∑ a, f a` are equal, but not by definition. With `sum f` both `domain` and `toFun` are made explicit. -/
def LinearPMap.sum : E →ₗ.[R] F where
  domain := ⨅ a, (f a).domain
  toFun := ∑ a, (f a).toFun ∘ₗ inclusion (fun _ _ ↦ by simp_all only [mem_iInf])
