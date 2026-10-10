import AFTD.Prelude
import AFTD.Kb.Tcs.KnillLaflamme

/-!
# LinearPMap.unitaryConj

Topic: quantum_mechanics   Node: 6e9fe046ecca

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.unitaryConj`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conjugation `u A u⁻¹` of a partially-defined operator `A : H →ₗ.[ℂ] H` by a unitary `u : H ≃ₗᵢ[ℂ] H'`, with domain `u (A.domain) = u⁻¹ ⁻¹' (A.domain)` and action `y ↦ u (A (u⁻¹ y))`. Since `u` and `u⁻¹` are `ℂ`-linear, the result is again `ℂ`-linear.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
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
/-- The conjugation `u A u⁻¹` of a partially-defined operator `A : H →ₗ.[ℂ] H` by a unitary `u : H ≃ₗᵢ[ℂ] H'`, with domain `u (A.domain) = u⁻¹ ⁻¹' (A.domain)` and action `y ↦ u (A (u⁻¹ y))`. Since `u` and `u⁻¹` are `ℂ`-linear, the result is again `ℂ`-linear. -/
def LinearPMap.unitaryConj : H' →ₗ.[ℂ] H' where
  domain := A.domain.comap (u.symm.toLinearEquiv : H' →ₗ[ℂ] H)
  toFun := u.toLinearEquiv.toLinearMap.comp <| A.toFun.comp
    (((u.symm.toLinearEquiv : H' →ₗ[ℂ] H).comp
      (A.domain.comap (u.symm.toLinearEquiv : H' →ₗ[ℂ] H)).subtype).codRestrict A.domain
        fun x => x.2)
