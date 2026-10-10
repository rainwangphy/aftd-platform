import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapStandardDeviation
import AFTD.Kb.Physics.LinearPMapVariance

/-!
# LinearPMap.standardDeviation_eq_sqrt_variance

Topic: quantum_mechanics   Node: 6a80b7f38a56

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.standardDeviation_eq_sqrt_variance`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard deviation, unfolded to the square root of the variance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The standard deviation, unfolded to the square root of the variance. -/
lemma LinearPMap.standardDeviation_eq_sqrt_variance (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    standardDeviation T ψ = Real.sqrt (variance T ψ) :=
  rfl
