import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapUnitaryConj
import AFTD.Kb.Physics.LinearPMapMemUnitaryConjDomainIff
import AFTD.Kb.Tcs.KnillLaflamme

/-!
# LinearPMap.IsFormalAdjoint.unitaryConj

Topic: quantum_mechanics   Node: ffb01ed84594

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsFormalAdjoint.unitaryConj`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unitary conjugation preserves formal adjointness. If `A` is a formal adjoint of `B`, then `u A u⁻¹` is a formal adjoint of `u B u⁻¹`. Unitary conjugation preserves symmetry when `A = B`.
-/

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
variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) in
variable {u A} in
open scoped InnerProductSpace in
/-- Unitary conjugation preserves formal adjointness. If `A` is a formal adjoint of `B`, then `u A u⁻¹` is a formal adjoint of `u B u⁻¹`. Unitary conjugation preserves symmetry when `A = B`. -/
lemma LinearPMap.IsFormalAdjoint.unitaryConj {B : H →ₗ.[ℂ] H} (h : A.IsFormalAdjoint B) :
    (unitaryConj u A).IsFormalAdjoint (unitaryConj u B) := by
  intro x y
  let x' : A.domain := ⟨u.symm (x : H'), (mem_unitaryConj_domain_iff u A).mp x.2⟩
  let y' : B.domain := ⟨u.symm (y : H'), (mem_unitaryConj_domain_iff u B).mp y.2⟩
  calc ⟪LinearPMap.unitaryConj u A x, (y : H')⟫_ℂ
      = ⟪A x', (y' : H)⟫_ℂ := u.inner_map_eq_flip _ _
    _ = ⟪(x' : H), B y'⟫_ℂ := h x' y'
    _ = ⟪(x : H'), LinearPMap.unitaryConj u B y⟫_ℂ := u.symm.inner_map_eq_flip _ _
