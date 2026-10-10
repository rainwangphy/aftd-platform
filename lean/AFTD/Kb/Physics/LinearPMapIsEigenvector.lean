import AFTD.Prelude

/-!
# LinearPMap.IsEigenvector

Topic: quantum_mechanics   Node: a988e72c7114

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsEigenvector`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/IsEigenvector.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonzero vector in the domain of `T` satisfying `T ψ = μ • ψ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- A nonzero vector in the domain of `T` satisfying `T ψ = μ • ψ`. -/
def LinearPMap.IsEigenvector (T : H →ₗ.[ℂ] H) (ψ : T.domain) (μ : ℂ) : Prop :=
  T ψ = μ • (ψ : H) ∧ (ψ : H) ≠ 0
