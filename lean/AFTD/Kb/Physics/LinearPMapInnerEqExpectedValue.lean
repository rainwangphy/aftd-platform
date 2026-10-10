import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapExpectedValueEqInner

/-!
# LinearPMap.inner_eq_expectedValue

Topic: quantum_mechanics   Node: 2e30de1b9bbf

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.inner_eq_expectedValue`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reverse orientation of `LinearPMap.expectedValue_eq_inner`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Reverse orientation of `LinearPMap.expectedValue_eq_inner`. -/
lemma LinearPMap.inner_eq_expectedValue (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric) (ψ : T.domain) :
    (expectedValue T ψ : ℂ) = ⟪(ψ : H), T ψ⟫_ℂ :=
  (expectedValue_eq_inner T hT ψ).symm
