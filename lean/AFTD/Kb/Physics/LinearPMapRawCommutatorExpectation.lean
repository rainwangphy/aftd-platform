import AFTD.Prelude

/-!
# LinearPMap.rawCommutatorExpectation

Topic: quantum_mechanics   Node: 4ad3cbf9055a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.rawCommutatorExpectation`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The expectation of the raw commutator `[A, B]` in the state `ψ`, with explicit second-order domain witnesses.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The expectation of the raw commutator `[A, B]` in the state `ψ`, with explicit second-order domain witnesses. -/
noncomputable def LinearPMap.rawCommutatorExpectation (A B : H →ₗ.[ℂ] H)
    (ψ : A.domain) (hψB : (ψ : H) ∈ B.domain)
    (hBA : A ψ ∈ B.domain) (hAB : B ⟨ψ, hψB⟩ ∈ A.domain) : ℂ :=
  ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ψ, hBA⟩⟫_ℂ
