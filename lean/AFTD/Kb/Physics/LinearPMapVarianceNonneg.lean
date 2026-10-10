import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapVarianceEqCenteredNormSq

/-!
# LinearPMap.variance_nonneg

Topic: quantum_mechanics   Node: 2781d490d56e

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.variance_nonneg`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Variance is nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Variance is nonnegative. -/
lemma LinearPMap.variance_nonneg (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    0 ≤ variance T ψ := by
  rw [variance_eq_centered_norm_sq]
  exact sq_nonneg _
