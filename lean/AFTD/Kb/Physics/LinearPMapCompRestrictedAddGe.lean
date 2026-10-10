import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapMemCompRestrictedDomainIff
import AFTD.Kb.Physics.LinearPMapMemDomainOfMemCompRestrictedDomain
import AFTD.Kb.Physics.LinearPMapSumApply
import AFTD.Kb.Physics.LinearPMapCompRestrictedApply

/-!
# LinearPMap.compRestricted_add_ge

Topic: classical_mechanics   Node: 9d7cddc00f31

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.compRestricted_add_ge`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.compRestricted_add_ge
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
lemma LinearPMap.compRestricted_add_ge : g ∘ᵣ f₁ + g ∘ᵣ f₂ ≤ g ∘ᵣ (f₁ + f₂) := by
  constructor
  · intro x hx
    obtain ⟨h₁, h₁'⟩ := mem_compRestricted_domain_iff.mp hx.1
    obtain ⟨h₂, h₂'⟩ := mem_compRestricted_domain_iff.mp hx.2
    exact mem_compRestricted_domain_iff.mpr ⟨⟨h₁, h₂⟩, add_mem h₁' h₂'⟩
  · intro x y hxy
    obtain ⟨h₁, h₁'⟩ := mem_compRestricted_domain_iff.mp x.2.1
    obtain ⟨h₂, h₂'⟩ := mem_compRestricted_domain_iff.mp x.2.2
    simp [← hxy, add_apply, ← g.map_add ⟨f₁ ⟨x, h₁⟩, h₁'⟩ ⟨f₂ ⟨x, h₂⟩, h₂'⟩]
