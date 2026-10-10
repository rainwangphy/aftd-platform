import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjoint
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointIsClosed
import AFTD.Kb.Physics.LinearPMapIsClosedClosureEq
import AFTD.Kb.Physics.LinearPMapIsUnbounded
import AFTD.Kb.Physics.LinearPMapAdjointAntitone
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapHasDenseDomainClosure
import AFTD.Kb.Physics.LinearPMapIsEssentiallySelfAdjointHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointClosureEqAdjoint
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointAdjointEqClosure
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointIsClosable

/-!
# LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension

Topic: quantum_mechanics   Node: 550228a2ef22

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The closure is the unique self-adjoint extension of an essentially self-adjoint operator.
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
/-- The closure is the unique self-adjoint extension of an essentially self-adjoint operator. -/
lemma LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension [CompleteSpace H]
    (h : T.IsEssentiallySelfAdjoint) {T₂ : H →ₗ.[ℂ] H} (h_le : T ≤ T₂) (h₂ : IsSelfAdjoint T₂) :
    T₂ = T.closure := by
  have h_cl : T₂.IsClosed := IsSelfAdjoint.isClosed h₂
  have h_le' : T.closure ≤ T₂ := h_cl.closure_eq ▸ h_cl.isClosable.closure_mono h_le
  exact eq_of_le_of_ge (h ▸ h₂ ▸ adjoint_antitone (Or.inl h.hasDenseDomain.closure) h_le') h_le'
