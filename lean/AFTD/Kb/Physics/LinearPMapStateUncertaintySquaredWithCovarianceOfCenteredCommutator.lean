import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCenteredCommutatorExpectation
import AFTD.Kb.Physics.LinearPMapCovariance
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapVarianceEqCenteredNormSq
import AFTD.Kb.Physics.LinearPMapInnerNormSqEqReSqAddCommutatorHalfSq
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq
import AFTD.Kb.Physics.LinearPMapCovarianceSelfEqVariance

/-!
# LinearPMap.state_uncertainty_squared_with_covariance_of_centered_commutator

Topic: quantum_mechanics   Node: 4b25a1804b0a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.state_uncertainty_squared_with_covariance_of_centered_commutator`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A centered commutator identity implies the Robertson–Schrödinger uncertainty bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
variable {c : ℝ} in
variable (h_centered : centeredCommutatorExpectation A B ψ hψB = Complex.I * c) in
include h_centered in
/-- A centered commutator identity implies the Robertson–Schrödinger uncertainty bound. -/
lemma LinearPMap.state_uncertainty_squared_with_covariance_of_centered_commutator :
    (covariance A B ψ hψB) ^ 2 + (c / 2) ^ 2 ≤
      variance A ψ * variance B ⟨ψ, hψB⟩ := by
  rw [variance_eq_centered_norm_sq, variance_eq_centered_norm_sq]
  rw [show ‖centered A ψ‖ ^ 2 * ‖centered B ⟨ψ, hψB⟩‖ ^ 2 =
    (‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖) ^ 2 by ring]
  calc
    (covariance A B ψ hψB) ^ 2 + (c / 2) ^ 2 =
        ‖⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ‖ ^ 2 := by
          rw [inner_norm_sq_eq_re_sq_add_commutator_half_sq
            (by simpa [centeredCommutatorExpectation] using h_centered)]
          rfl
    _ ≤ (‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖) ^ 2 := by
        have h_bound :=
          norm_inner_le_norm (𝕜 := ℂ) (centered A ψ) (centered B ⟨ψ, hψB⟩)
        have h_inner_nonneg : 0 ≤ ‖⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ‖ :=
          norm_nonneg _
        have h_mul_nonneg : 0 ≤ ‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith
