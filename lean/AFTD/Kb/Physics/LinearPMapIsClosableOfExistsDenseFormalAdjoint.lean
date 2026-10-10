import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleAdjointAdjointIffMemSubmoduleToLpOrthogonalOrthogonal
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleMemSubmoduleIffMemSubmoduleToLp
import AFTD.Kb.Physics.InnerProductSpaceSubmoduleSubmoduleToLpClosure

/-!
# LinearPMap.isClosable_of_exists_dense_formalAdjoint

Topic: quantum_mechanics   Node: 85b0e70fc32d

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isClosable_of_exists_dense_formalAdjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A LinearPMap with densely-defined formal adjoint is closable.
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
/-- A LinearPMap with densely-defined formal adjoint is closable. -/
lemma LinearPMap.isClosable_of_exists_dense_formalAdjoint [CompleteSpace H] [CompleteSpace H']
    (h : U.HasDenseDomain) (h_fadj : ∃ U' : H' →ₗ.[ℂ] H, U'.HasDenseDomain ∧ U'.IsFormalAdjoint U) :
    U.IsClosable := by
  have h_adj : U†.HasDenseDomain := by
    obtain ⟨U', hU', hU''⟩ := h_fadj
    exact hU'.mono (hU''.symm.le_adjoint h).1
  use U††
  ext
  rw [adjoint_graph_eq_graph_adjoint h_adj, adjoint_graph_eq_graph_adjoint h,
    mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_iff_mem_submoduleToLp, submoduleToLp_closure]
