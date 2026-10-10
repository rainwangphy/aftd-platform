import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain

/-!
# LinearPMap.adjoint_antitone

Topic: quantum_mechanics   Node: 667d5a0a02e0

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_antitone`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_antitone
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
lemma LinearPMap.adjoint_antitone [CompleteSpace H]
    (h₁₂ : U₁.HasDenseDomain ∨ ¬U₂.HasDenseDomain) (h_le : U₁ ≤ U₂) : U₂† ≤ U₁† := by
  have h_agree : ∀ w : U₁.domain, U₁ w = U₂ ⟨w, h_le.1 w.2⟩ := fun w ↦ @h_le.2 w ⟨w, h_le.1 w.2⟩ rfl
  constructor
  · intro v
    let f₁ : U₁.domain → ℂ := fun w ↦ ⟪v, U₁ w⟫_ℂ
    let f₂ : U₂.domain → ℂ := fun w ↦ ⟪v, U₂ w⟫_ℂ
    change Continuous f₂ → Continuous f₁
    suffices f₁ = fun w : U₁.domain ↦ f₂ ⟨w, h_le.1 w.2⟩ by rw [this]; fun_prop
    simp [f₁, f₂, h_agree]
  · intro u v huv
    rcases h₁₂ with (h₁ | h₂)
    · have h₂ : U₂.HasDenseDomain := h₁.mono h_le.1
      refine (adjoint_apply_eq h₁ v fun w ↦ ?_).symm
      rw [adjoint_isFormalAdjoint h₂ u ⟨w, h_le.1 w.2⟩, h_agree, huv]
    · have h₁ : ¬U₁.HasDenseDomain := fun h ↦ h₂ (h.mono h_le.1)
      rw [adjoint_apply_of_not_dense h₁ v, adjoint_apply_of_not_dense h₂ u]
