import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapStandardDeviation
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapStandardDeviationEqSqrtVariance
import AFTD.Kb.Physics.LinearPMapVarianceNonneg

/-!
# LinearPMap.standardDeviation_sq

Topic: quantum_mechanics   Node: 2ee2048993f6

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.standardDeviation_sq`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.standardDeviation_sq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
@[simp]
lemma LinearPMap.standardDeviation_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    standardDeviation T ψ ^ 2 = variance T ψ := by
  rw [standardDeviation_eq_sqrt_variance, Real.sq_sqrt]
  exact variance_nonneg T ψ
