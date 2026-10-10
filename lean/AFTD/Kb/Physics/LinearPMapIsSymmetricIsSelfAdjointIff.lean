import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsSymmetricIffLeAdjoint

/-!
# LinearPMap.IsSymmetric.isSelfAdjoint_iff

Topic: quantum_mechanics   Node: 5971529d38f6

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.isSelfAdjoint_iff`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.isSelfAdjoint_iff
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
lemma LinearPMap.IsSymmetric.isSelfAdjoint_iff [CompleteSpace H] (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    IsSelfAdjoint T ↔ T†.domain = T.domain := by
  constructor <;> intro h''
  · congr
  · exact (eq_of_le_of_domain_eq ((isSymmetric_iff_le_adjoint h').mp h) h''.symm).symm
