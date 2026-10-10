import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapCenteredEq

/-!
# LinearPMap.centered_eq_zero_iff

Topic: quantum_mechanics   Node: c529c5233910

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.centered_eq_zero_iff`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A centered vector vanishes exactly when `Tψ = ⟨T⟩_ψ ψ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- A centered vector vanishes exactly when `Tψ = ⟨T⟩_ψ ψ`. -/
lemma LinearPMap.centered_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    centered T ψ = 0 ↔ T ψ = (expectedValue T ψ : ℂ) • (ψ : H) := by
  rw [centered_eq, sub_eq_zero]
