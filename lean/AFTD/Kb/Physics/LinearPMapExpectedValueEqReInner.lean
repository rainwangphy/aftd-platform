import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapExpectedValue

/-!
# LinearPMap.expectedValue_eq_re_inner

Topic: quantum_mechanics   Node: 789df424b10b

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.expectedValue_eq_re_inner`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The expectation value, unfolded as a real part.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The expectation value, unfolded as a real part. -/
lemma LinearPMap.expectedValue_eq_re_inner (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    expectedValue T ψ = (⟪(ψ : H), T ψ⟫_ℂ).re :=
  rfl
