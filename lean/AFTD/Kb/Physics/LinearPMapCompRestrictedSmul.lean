import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapMemCompRestrictedDomainIff
import AFTD.Kb.Physics.LinearPMapSumApply

/-!
# LinearPMap.compRestricted_smul

Topic: classical_mechanics   Node: f80085bd0ec0

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.compRestricted_smul`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.compRestricted_smul
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
lemma LinearPMap.compRestricted_smul {S : Type*} [DivisionRing S]
    [Module S E] [Module S F] [Module S G] [SMulCommClass S S F] [SMulCommClass S S G]
    {c : S} (hc : c ≠ 0) (g : F →ₗ.[S] G) (f : E →ₗ.[S] F) :
    g ∘ᵣ (c • f) = c • (g ∘ᵣ f) := by
  ext x hx hx'
  · simp [mem_compRestricted_domain_iff, g.domain.smul_mem_iff hc]
  · obtain ⟨h, h'⟩ := mem_compRestricted_domain_iff.mp (smul_domain c (g ∘ᵣ f) ▸ hx')
    exact g.toFun.map_smul c ⟨f ⟨x, h⟩, h'⟩
