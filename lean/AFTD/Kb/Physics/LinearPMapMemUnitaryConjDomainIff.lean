import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapUnitaryConj

/-!
# LinearPMap.mem_unitaryConj_domain_iff

Topic: quantum_mechanics   Node: bccb660f69cf

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.mem_unitaryConj_domain_iff`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Membership in the conjugated domain: `x ∈ D(u A u⁻¹) ↔ u⁻¹ x ∈ D(A)`.
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
/-- Membership in the conjugated domain: `x ∈ D(u A u⁻¹) ↔ u⁻¹ x ∈ D(A)`. -/
lemma LinearPMap.mem_unitaryConj_domain_iff {x : H'} :
    x ∈ (unitaryConj u A).domain ↔ u.symm x ∈ A.domain := Iff.rfl
