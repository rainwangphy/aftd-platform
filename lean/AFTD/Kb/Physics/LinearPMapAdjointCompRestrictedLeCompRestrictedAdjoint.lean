import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapCompRestrictedDomainLe
import AFTD.Kb.Physics.LinearPMapMemDomainOfMemCompRestrictedDomain
import AFTD.Kb.Physics.LinearPMapSumApply
import AFTD.Kb.Physics.LinearPMapCompRestrictedApply

/-!
# LinearPMap.adjoint_compRestricted_le_compRestricted_adjoint

Topic: quantum_mechanics   Node: 0110761ecc33

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_compRestricted_le_compRestricted_adjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_compRestricted_le_compRestricted_adjoint
-/

set_option quotPrecheck false
open LinearPMap
@[inherit_doc compRestricted]
local infixr:80 " ∘ᵣ " => compRestricted

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
open InnerProductSpace in
open Complex ComplexConjugate in
variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''} in
lemma LinearPMap.adjoint_compRestricted_le_compRestricted_adjoint [CompleteSpace H] [CompleteSpace H']
    (hV : V.HasDenseDomain) (hVU : (V ∘ᵣ U).HasDenseDomain) : U† ∘ᵣ V† ≤ (V ∘ᵣ U)† := by
  have hU : U.HasDenseDomain := hVU.mono (compRestricted_domain_le V U)
  have h : (U† ∘ᵣ V†).IsFormalAdjoint (V ∘ᵣ U) := by
    intro x y
    have hx := mem_domain_of_mem_compRestricted_domain x
    have hy := mem_domain_of_mem_compRestricted_domain y
    trans ⟪V† ⟨x, x.2.2⟩, U ⟨y, y.2.2⟩⟫_ℂ
    · exact adjoint_isFormalAdjoint hU ⟨V† ⟨x, x.2.2⟩, hx⟩ ⟨y, y.2.2⟩
    exact adjoint_isFormalAdjoint hV ⟨x, x.2.2⟩ ⟨U ⟨y, y.2.2⟩, hy⟩
  exact ⟨fun x hx ↦ mem_adjoint_domain_of_exists _ ⟨(U† ∘ᵣ V†) ⟨x, hx⟩, h ⟨x, hx⟩⟩,
    fun x y hxy ↦ (adjoint_apply_eq hVU y <| hxy ▸ h x).symm⟩
