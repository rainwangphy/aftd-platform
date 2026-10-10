import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapSum
import AFTD.Kb.Physics.LinearPMapSumDomainLe

/-!
# LinearPMap.sum_apply

Topic: classical_mechanics   Node: bd0621cc1fa7

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sum_apply`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sum_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable {α : Type*} [Fintype α] (f : α → E →ₗ.[R] F) in
@[simp]
lemma LinearPMap.sum_apply (ψ : (sum f).domain) : sum f ψ = ∑ a, f a ⟨ψ, sum_domain_le f a ψ.2⟩ :=
  LinearMap.sum_apply Finset.univ (fun a ↦ (f a).toFun ∘ₗ inclusion (sum_domain_le f a)) ψ
