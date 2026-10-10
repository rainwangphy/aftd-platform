import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain

/-!
# LinearPMap.adjoint_smul

Topic: quantum_mechanics   Node: 32a1197e7495

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_smul`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_smul
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
@[simp]
lemma LinearPMap.adjoint_smul [CompleteSpace H] (U : H →ₗ.[ℂ] H') {c : ℂ} (hc : c ≠ 0) :
    (c • U)† = conj c • U† := by
  refine dExt ?_ fun x y hxy ↦ ?_
  · ext x
    change Continuous (fun w ↦ ⟪x, c • U w⟫_ℂ) ↔ Continuous (fun w ↦ ⟪x, U w⟫_ℂ)
    exact Iff.trans (by simp [inner_smul_right]) (continuous_const_smul_iff₀ hc)
  · by_cases h : U.HasDenseDomain
    · refine adjoint_apply_eq (smul_domain c U ▸ h) x fun w ↦ ?_
      simp [inner_smul_left, inner_smul_right, adjoint_isFormalAdjoint h y w, hxy]
    · simp [adjoint_apply_of_not_dense h y, adjoint_apply_of_not_dense (smul_domain c U ▸ h) x]
