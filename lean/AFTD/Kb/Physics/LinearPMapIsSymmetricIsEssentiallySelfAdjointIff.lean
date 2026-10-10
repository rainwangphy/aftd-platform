import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjoint
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjointDef
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointClosureEqAdjoint
import AFTD.Kb.Physics.LinearPMapIsUnbounded
import AFTD.Kb.Physics.LinearPMapIsSymmetricIsUnboundedIffHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsSymmetricClosureLeAdjoint
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointAdjointEqClosure
import AFTD.Kb.Physics.LinearPMapHasDenseDomainClosure
import AFTD.Kb.Physics.LinearPMapIsSymmetricClosure

/-!
# LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_iff

Topic: quantum_mechanics   Node: 71a3c460c9cb

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_iff`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
open InnerProductSpace in
open InnerProductSpaceSubmodule in
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
lemma LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_iff [CompleteSpace H]
    (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    T.IsEssentiallySelfAdjoint ↔ T†.domain = T.closure.domain := by
  rw [isEssentiallySelfAdjoint_def, isSelfAdjoint_def,
    (h.isUnbounded_iff_hasDenseDomain.mpr h').adjoint_closure_eq_adjoint]
  constructor <;> intro h''
  · congr
  · exact (eq_of_le_of_domain_eq (h.closure_le_adjoint h') h''.symm).symm
