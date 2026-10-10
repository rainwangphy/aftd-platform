import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapCompRestrictedAssoc
import AFTD.Kb.Physics.LinearPMapMemCompRestrictedDomainIff
import AFTD.Kb.Physics.LinearPMapSumApply

/-!
# LinearPMap.instMonoid

Topic: classical_mechanics   Node: 66f1be486c5f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.instMonoid`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.instMonoid
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
instance LinearPMap.instMonoid : Monoid (E →ₗ.[R] E) where
  mul := compRestricted
  mul_assoc := compRestricted_assoc
  one := ⟨⊤, topEquiv.toLinearMap⟩
  one_mul f := by
    change ⟨⊤, topEquiv.toLinearMap⟩ ∘ᵣ f = f
    ext
    · simp [mem_compRestricted_domain_iff]
    · rfl
  mul_one f := by
    change f ∘ᵣ ⟨⊤, topEquiv.toLinearMap⟩ = f
    ext
    · simp [mem_compRestricted_domain_iff]
    · rfl
