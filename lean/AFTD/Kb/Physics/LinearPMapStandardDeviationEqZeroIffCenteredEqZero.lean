import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapStandardDeviation
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapStandardDeviationEqSqrtVariance
import AFTD.Kb.Physics.LinearPMapVarianceNonneg
import AFTD.Kb.Physics.LinearPMapVarianceEqZeroIffCenteredEqZero
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq

/-!
# LinearPMap.standardDeviation_eq_zero_iff_centered_eq_zero

Topic: quantum_mechanics   Node: 2aaacbd250b0

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.standardDeviation_eq_zero_iff_centered_eq_zero`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Zero standard deviation is the same as a zero centered vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Zero standard deviation is the same as a zero centered vector. -/
lemma LinearPMap.standardDeviation_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) :
    standardDeviation T ψ = 0 ↔ centered T ψ = 0 := by
  rw [standardDeviation_eq_sqrt_variance, Real.sqrt_eq_zero]
  · exact variance_eq_zero_iff_centered_eq_zero T ψ
  · exact variance_nonneg T ψ
