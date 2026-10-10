import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapCompRestrictedAssoc
import AFTD.Kb.Physics.LinearPMapMemDomainOfMemCompRestrictedDomain
import AFTD.Kb.Physics.LinearPMapSumApply
import AFTD.Kb.Physics.LinearPMapCompRestrictedApply

/-!
# LinearPMap.IsSymmetric.pow

Topic: quantum_mechanics   Node: 0cd8b6dbd2f1

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.pow`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.pow
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
@[aesop safe apply]
lemma LinearPMap.IsSymmetric.pow (h : T.IsSymmetric) (n : ℕ) : (T ^ n).IsSymmetric := by
  induction n with
  | zero => exact fun _ _ ↦ rfl
  | succ n ih =>
    intro x y
    let y' : (T * T ^ n).domain := ⟨y, pow_succ' T n ▸ y.2⟩
    let Tx : (T ^ n).domain := ⟨T ⟨x, x.2.2⟩, mem_domain_of_mem_compRestricted_domain x⟩
    let Tny : T.domain := ⟨(T ^ n) ⟨y', y'.2.2⟩, mem_domain_of_mem_compRestricted_domain y'⟩
    have h_eq : T Tny = (T ^ (n + 1)) y := by
      change (T * T ^ n) y' = (T ^ (n + 1)) y
      congr 1
      · exact (pow_succ' T n).symm
      · exact (Subtype.heq_iff_coe_eq <| by simp [pow_succ']).mpr rfl
    exact (ih Tx ⟨y', y'.2.2⟩).trans (h_eq ▸ h ⟨x, x.2.2⟩ Tny)
