import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapVarianceEqCenteredNormSq

/-!
# LinearPMap.variance_eq_zero_iff_centered_eq_zero

Topic: quantum_mechanics   Node: 9bb136a523cc

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.variance_eq_zero_iff_centered_eq_zero`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Zero variance is the same as a zero centered vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Zero variance is the same as a zero centered vector. -/
lemma LinearPMap.variance_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ = 0 ↔ centered T ψ = 0 := by
  rw [variance_eq_centered_norm_sq]
  exact sq_eq_zero_iff.trans norm_eq_zero
