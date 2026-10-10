import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapStandardDeviation
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapStandardDeviationEqSqrtVariance

/-!
# LinearPMap.standardDeviation_nonneg

Topic: quantum_mechanics   Node: de567d699327

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.standardDeviation_nonneg`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Standard deviation is nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Standard deviation is nonnegative. -/
lemma LinearPMap.standardDeviation_nonneg (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    0 ≤ standardDeviation T ψ := by
  rw [standardDeviation_eq_sqrt_variance]
  exact Real.sqrt_nonneg _
