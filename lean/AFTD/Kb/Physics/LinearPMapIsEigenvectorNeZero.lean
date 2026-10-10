import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsEigenvector

/-!
# LinearPMap.IsEigenvector.ne_zero

Topic: quantum_mechanics   Node: 9fc4b5dff8c6

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsEigenvector.ne_zero`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/IsEigenvector.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A partial-map eigenvector is nonzero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- A partial-map eigenvector is nonzero. -/
lemma LinearPMap.IsEigenvector.ne_zero {T : H →ₗ.[ℂ] H} {ψ : T.domain} {μ : ℂ}
    (hψ : T.IsEigenvector ψ μ) :
    (ψ : H) ≠ 0 :=
  hψ.2
