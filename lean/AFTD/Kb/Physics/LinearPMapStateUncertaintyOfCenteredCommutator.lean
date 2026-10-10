import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCenteredCommutatorExpectation
import AFTD.Kb.Physics.LinearPMapStandardDeviation
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapStateUncertaintySquaredOfCenteredCommutator
import AFTD.Kb.Physics.LinearPMapSqrtMulLeOfSqLe
import AFTD.Kb.Physics.LinearPMapVarianceNonneg
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq
import AFTD.Kb.Physics.LinearPMapCovarianceSelfEqVariance

/-!
# LinearPMap.state_uncertainty_of_centered_commutator

Topic: quantum_mechanics   Node: 6d7ef6b11cfa

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.state_uncertainty_of_centered_commutator`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A centered commutator identity implies the standard uncertainty bound.
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
/-- A centered commutator identity implies the standard uncertainty bound. -/
lemma LinearPMap.state_uncertainty_of_centered_commutator :
    |c| / 2 ≤ standardDeviation A ψ * standardDeviation B ⟨ψ, hψB⟩ := by
  have h_sq := state_uncertainty_squared_of_centered_commutator A B ψ hψB h_centered
  refine sqrt_mul_le_of_sq_le (variance_nonneg A ψ) (by positivity) ?_
  simpa [standardDeviation] using h_sq
