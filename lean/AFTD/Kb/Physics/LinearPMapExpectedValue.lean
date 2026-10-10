import AFTD.Prelude

/-!
# LinearPMap.expectedValue

Topic: quantum_mechanics   Node: 0486c5002fd2

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.expectedValue`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expectation value `re ⟪ψ, Tψ⟫_ℂ` for `ψ ∈ T.domain`. For symmetric `T`, this agrees with `⟪ψ, Tψ⟫_ℂ` after coercion from `ℝ`; see `expectedValue_eq_inner`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- Expectation value `re ⟪ψ, Tψ⟫_ℂ` for `ψ ∈ T.domain`. For symmetric `T`, this agrees with `⟪ψ, Tψ⟫_ℂ` after coercion from `ℝ`; see `expectedValue_eq_inner`. -/
noncomputable def LinearPMap.expectedValue (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  (⟪(ψ : H), T ψ⟫_ℂ).re
