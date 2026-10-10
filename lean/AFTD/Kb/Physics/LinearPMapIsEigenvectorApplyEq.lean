import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsEigenvector

/-!
# LinearPMap.IsEigenvector.apply_eq

Topic: quantum_mechanics   Node: 769a8fe2be02

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsEigenvector.apply_eq`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/IsEigenvector.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The eigenvalue equation for a partial-map eigenvector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The eigenvalue equation for a partial-map eigenvector. -/
lemma LinearPMap.IsEigenvector.apply_eq {T : H →ₗ.[ℂ] H} {ψ : T.domain} {μ : ℂ}
    (hψ : T.IsEigenvector ψ μ) :
    T ψ = μ • (ψ : H) :=
  hψ.1
