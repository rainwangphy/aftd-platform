import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCenteredCommutatorExpectation
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapVarianceEqCenteredNormSq
import AFTD.Kb.Physics.LinearPMapCommutatorHalfSqLeMulNormSq
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq
import AFTD.Kb.Physics.LinearPMapCovarianceSelfEqVariance

/-!
# LinearPMap.state_uncertainty_squared_of_centered_commutator

Topic: quantum_mechanics   Node: 15cfed59b071

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.state_uncertainty_squared_of_centered_commutator`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A centered commutator identity implies the squared Robertson uncertainty bound.
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
/-- A centered commutator identity implies the squared Robertson uncertainty bound. -/
lemma LinearPMap.state_uncertainty_squared_of_centered_commutator :
    (|c| / 2) ^ 2 ≤ variance A ψ * variance B ⟨ψ, hψB⟩ := by
  rw [variance_eq_centered_norm_sq, variance_eq_centered_norm_sq]
  rw [show ‖centered A ψ‖ ^ 2 * ‖centered B ⟨ψ, hψB⟩‖ ^ 2 =
    (‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖) ^ 2 by ring]
  exact commutator_half_sq_le_mul_norm_sq (by simpa [centeredCommutatorExpectation] using
    h_centered)
