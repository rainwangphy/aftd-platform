import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsUnbounded
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjoint
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleAdjointAdjointIffMemSubmoduleToLpOrthogonalOrthogonal
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleClosureIffMemSubmoduleToLpClosure
import AFTD.Kb.Physics.LinearPMapIsUnboundedAdjointClosureEqAdjoint
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId

/-!
# LinearPMap.IsUnbounded.adjoint_adjoint_eq_closure

Topic: quantum_mechanics   Node: 940a14adc7a5

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsUnbounded.adjoint_adjoint_eq_closure`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsUnbounded.adjoint_adjoint_eq_closure
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
@[simp]
lemma LinearPMap.IsUnbounded.adjoint_adjoint_eq_closure [CompleteSpace H] [CompleteSpace H']
    (h : U.IsUnbounded) :
    U†† = U.closure := by
  refine eq_of_eq_graph ?_
  ext
  rw [adjoint_graph_eq_graph_adjoint h.adjoint.1, adjoint_graph_eq_graph_adjoint h.1,
    ← IsClosable.graph_closure_eq_closure_graph h.2,
    mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_closure_iff_mem_submoduleToLp_closure]
