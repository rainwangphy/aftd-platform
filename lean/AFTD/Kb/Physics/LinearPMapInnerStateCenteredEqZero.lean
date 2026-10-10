import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapCenteredEq
import AFTD.Kb.Physics.LinearPMapExpectedValueEqInner

/-!
# LinearPMap.inner_state_centered_eq_zero

Topic: quantum_mechanics   Node: 51135878ee0c

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.inner_state_centered_eq_zero`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a unit vector and symmetric `T`, the centered vector is orthogonal to the state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- For a unit vector and symmetric `T`, the centered vector is orthogonal to the state. -/
lemma LinearPMap.inner_state_centered_eq_zero (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    ⟪(ψ : H), centered T ψ⟫_ℂ = 0 := by
  rw [centered_eq, inner_sub_right, inner_smul_right, expectedValue_eq_inner T hT ψ]
  simp [hψ_norm, inner_self_eq_norm_sq_to_K]
