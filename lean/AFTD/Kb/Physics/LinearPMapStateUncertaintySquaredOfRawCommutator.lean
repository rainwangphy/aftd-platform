import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapRawCommutatorExpectation
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapStateUncertaintySquaredOfCenteredCommutator
import AFTD.Kb.Physics.LinearPMapInnerCenteredCommutatorOfRawCommutator
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq
import AFTD.Kb.Physics.LinearPMapCovarianceSelfEqVariance

/-!
# LinearPMap.state_uncertainty_squared_of_raw_commutator

Topic: quantum_mechanics   Node: 034a6e670fbb

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.state_uncertainty_squared_of_raw_commutator`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A raw commutator expectation implies the squared Robertson uncertainty bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
variable (hψ_norm : ‖(ψ : H)‖ = 1) in
variable (hBA : A ψ ∈ B.domain) in
variable (hAB : B ⟨ψ, hψB⟩ ∈ A.domain) in
variable {c : ℝ} in
variable (h_raw : rawCommutatorExpectation A B ψ hψB hBA hAB = Complex.I * c) in
include hA hB hψ_norm hBA hAB h_raw in
/-- A raw commutator expectation implies the squared Robertson uncertainty bound. -/
lemma LinearPMap.state_uncertainty_squared_of_raw_commutator :
    (|c| / 2) ^ 2 ≤ variance A ψ * variance B ⟨ψ, hψB⟩ :=
  state_uncertainty_squared_of_centered_commutator A B ψ hψB
    (inner_centered_commutator_of_raw_commutator A B hA hB ψ hψB hψ_norm hBA hAB h_raw)
