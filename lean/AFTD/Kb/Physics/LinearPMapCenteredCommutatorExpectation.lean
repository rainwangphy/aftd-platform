import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCentered

/-!
# LinearPMap.centeredCommutatorExpectation

Topic: quantum_mechanics   Node: 758783aaa181

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.centeredCommutatorExpectation`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The scalar commutator of the centered vectors of `A` and `B` in the state `ψ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The scalar commutator of the centered vectors of `A` and `B` in the state `ψ`. -/
noncomputable def LinearPMap.centeredCommutatorExpectation (A B : H →ₗ.[ℂ] H)
    (ψ : A.domain) (hψB : (ψ : H) ∈ B.domain) : ℂ :=
  ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ -
    ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ
