import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapVariance

/-!
# LinearPMap.standardDeviation

Topic: quantum_mechanics   Node: bf27c6507b6a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.standardDeviation`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Standard deviation `√(variance)` for `ψ ∈ T.domain`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Standard deviation `√(variance)` for `ψ ∈ T.domain`. -/
noncomputable def LinearPMap.standardDeviation (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  Real.sqrt (variance T ψ)
