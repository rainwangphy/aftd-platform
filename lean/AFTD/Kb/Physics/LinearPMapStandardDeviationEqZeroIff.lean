import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapStandardDeviation
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapStandardDeviationEqZeroIffCenteredEqZero
import AFTD.Kb.Physics.LinearPMapCenteredEqZeroIff
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq

/-!
# LinearPMap.standardDeviation_eq_zero_iff

Topic: quantum_mechanics   Node: 7992f57c1ad5

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.standardDeviation_eq_zero_iff`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Zero standard deviation is the same as `Tψ = ⟨T⟩_ψ ψ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Zero standard deviation is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma LinearPMap.standardDeviation_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    standardDeviation T ψ = 0 ↔ T ψ = (expectedValue T ψ : ℂ) • (ψ : H) := by
  rw [standardDeviation_eq_zero_iff_centered_eq_zero, centered_eq_zero_iff]
