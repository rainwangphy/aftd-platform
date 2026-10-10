import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsUnbounded
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapHasDenseDomainClosure
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleClosureAdjointIffMemSubmoduleToLpClosureOrthogonal
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleAdjointIffMemSubmoduleToLpOrthogonal
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId

/-!
# LinearPMap.IsUnbounded.adjoint_closure_eq_adjoint

Topic: quantum_mechanics   Node: 85a93b37831f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsUnbounded.adjoint_closure_eq_adjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsUnbounded.adjoint_closure_eq_adjoint
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
lemma LinearPMap.IsUnbounded.adjoint_closure_eq_adjoint [CompleteSpace H] (h : U.IsUnbounded) :
    U.closure† = U† := by
  refine eq_of_eq_graph ?_
  ext
  rw [adjoint_graph_eq_graph_adjoint h.1, adjoint_graph_eq_graph_adjoint h.1.closure,
    ← IsClosable.graph_closure_eq_closure_graph h.2,
    mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal, orthogonal_closure,
    mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]
