import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCovariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapCovarianceEqReInnerCentered

/-!
# LinearPMap.covariance_comm

Topic: quantum_mechanics   Node: 12a818d1b016

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.covariance_comm`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Covariance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Swapping the two observables does not change the covariance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
/-- Swapping the two observables does not change the covariance. -/
lemma LinearPMap.covariance_comm :
    covariance A B ψ hψB = covariance B A ⟨ψ, hψB⟩ ψ.2 := by
  rw [covariance_eq_re_inner_centered, covariance_eq_re_inner_centered]
  calc
    (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re =
        (((starRingEnd ℂ) ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ)).re := by
      rw [inner_conj_symm]
    _ = (⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re := by
      change (star ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re =
        (⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re
      rw [Complex.star_def, Complex.conj_re]
