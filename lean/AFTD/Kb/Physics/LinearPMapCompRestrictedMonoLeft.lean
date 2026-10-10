import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapMemCompRestrictedDomainIff
import AFTD.Kb.Physics.LinearPMapMemDomainOfMemCompRestrictedDomain
import AFTD.Kb.Physics.LinearPMapSumApply
import AFTD.Kb.Physics.LinearPMapCompRestrictedApply

/-!
# LinearPMap.compRestricted_mono_left

Topic: classical_mechanics   Node: 2e7cd266f987

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.compRestricted_mono_left`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.compRestricted_mono_left
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
lemma LinearPMap.compRestricted_mono_left {g g' : F →ₗ.[R] G} (h : g ≤ g') (f : E →ₗ.[R] F) :
    g ∘ᵣ f ≤ g' ∘ᵣ f := by
  constructor
  · intro x hx
    obtain ⟨hx', hfx⟩ := mem_compRestricted_domain_iff.mp hx
    exact mem_compRestricted_domain_iff.mpr ⟨hx', h.1 hfx⟩
  · intro x y hxy
    exact @h.2 ⟨f ⟨x, x.2.2⟩, mem_domain_of_mem_compRestricted_domain x⟩
      ⟨f ⟨y, y.2.2⟩, mem_domain_of_mem_compRestricted_domain y⟩ (by simp [hxy])
