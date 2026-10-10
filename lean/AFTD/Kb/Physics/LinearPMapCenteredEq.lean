import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapExpectedValue

/-!
# LinearPMap.centered_eq

Topic: quantum_mechanics   Node: 22d303764732

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.centered_eq`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The centered vector, unfolded to its raw expression.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The centered vector, unfolded to its raw expression. -/
lemma LinearPMap.centered_eq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    centered T ψ = T ψ - (expectedValue T ψ : ℂ) • (ψ : H) :=
  rfl
