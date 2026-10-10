import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsUnbounded
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleClosureIffMemSubmoduleToLpClosure
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleAdjointAdjointIffMemSubmoduleToLpOrthogonalOrthogonal
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleAdjointIffMemSubmoduleToLpOrthogonal
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId

/-!
# LinearPMap.IsUnbounded.adjoint

Topic: quantum_mechanics   Node: 6146b25d80be

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsUnbounded.adjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsUnbounded.adjoint
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
lemma LinearPMap.IsUnbounded.adjoint [CompleteSpace H] [CompleteSpace H'] (h : U.IsUnbounded) :
    U†.IsUnbounded := by
  refine ⟨?_, (adjoint_isClosed h.1).isClosable⟩
  by_contra h_adj
  obtain ⟨y, hy⟩ := not_forall.mp h_adj
  have h_ne_bot : U†.domainᗮ = ⊥ → False := by
    rw [← orthogonal_eq_top_iff, orthogonal_orthogonal_eq_closure]
    exact fun a ↦ ne_of_mem_of_not_mem' mem_top hy a.symm
  obtain ⟨x, hx, hx'⟩ := exists_mem_ne_zero_of_ne_bot h_ne_bot
  apply hx'
  refine graph_fst_eq_zero_snd U.closure ?_ rfl
  rw [← IsClosable.graph_closure_eq_closure_graph h.2,
    mem_submodule_closure_iff_mem_submoduleToLp_closure, ← orthogonal_orthogonal_eq_closure,
    ← mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    ← adjoint_graph_eq_graph_adjoint h.1, mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]
  rintro ⟨y, Uy⟩ hy
  simp only [neg_zero, WithLp.prod_inner_apply, inner_zero_right, add_zero]
  exact hx y (mem_domain_of_mem_graph hy)
