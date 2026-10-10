import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapCentered

/-!
# LinearPMap.variance_eq_centered_norm_sq

Topic: quantum_mechanics   Node: 9ec68854ab91

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.variance_eq_centered_norm_sq`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The variance is the squared norm of the centered vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The variance is the squared norm of the centered vector. -/
lemma LinearPMap.variance_eq_centered_norm_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ = ‖centered T ψ‖ ^ 2 :=
  rfl
