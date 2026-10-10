import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsUnbounded
import AFTD.Kb.Physics.LinearPMapHasDenseDomainOrthogonalRange
import AFTD.Kb.Physics.LinearPMapIsUnboundedHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjoint
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointAdjointEqClosure
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointClosureEqAdjoint

/-!
# LinearPMap.IsUnbounded.orthogonal_adjoint_range

Topic: quantum_mechanics   Node: 008dc7b13ffa

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsUnbounded.orthogonal_adjoint_range`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`U†.rangeᗮ = U.closure.ker`
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
/-- `U†.rangeᗮ = U.closure.ker` -/
lemma LinearPMap.IsUnbounded.orthogonal_adjoint_range [CompleteSpace H] [CompleteSpace H']
    (h : U.IsUnbounded) : U†.toFun.rangeᗮ = U.closure.toFun.ker.map U.closure.domain.subtype :=
  h.adjoint_adjoint_eq_closure ▸ h.adjoint.hasDenseDomain.orthogonal_range
