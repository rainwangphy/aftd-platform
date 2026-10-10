import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain

/-!
# LinearPMap.adjoint_add_le_add_adjoint

Topic: quantum_mechanics   Node: ec552ecb5198

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_add_le_add_adjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_add_le_add_adjoint
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
lemma LinearPMap.adjoint_add_le_add_adjoint [CompleteSpace H]
    (U₁ U₂ : H →ₗ.[ℂ] H') (h₁₂ : (U₁ + U₂).HasDenseDomain) : U₁† + U₂† ≤ (U₁ + U₂)† := by
  have h₁ : U₁.HasDenseDomain := h₁₂.mono Set.inter_subset_left
  have h₂ : U₂.HasDenseDomain := h₁₂.mono Set.inter_subset_right
  constructor
  · intro u hu
    refine mem_adjoint_domain_of_exists _ ⟨U₁† ⟨u, hu.1⟩ + U₂† ⟨u, hu.2⟩, fun x ↦ ?_⟩
    simp only [add_apply, inner_add_left, inner_add_right,
      adjoint_isFormalAdjoint h₁ ⟨u, hu.1⟩ ⟨x, x.2.1⟩,
      adjoint_isFormalAdjoint h₂ ⟨u, hu.2⟩ ⟨x, x.2.2⟩]
  · intro u v huv
    refine (adjoint_apply_eq h₁₂ _ fun w ↦ ?_).symm
    simp only [add_apply, inner_add_left, inner_add_right, ← huv,
      adjoint_isFormalAdjoint h₁ ⟨u, u.2.1⟩ ⟨w, w.2.1⟩,
      adjoint_isFormalAdjoint h₂ ⟨u, u.2.2⟩ ⟨w, w.2.2⟩]
