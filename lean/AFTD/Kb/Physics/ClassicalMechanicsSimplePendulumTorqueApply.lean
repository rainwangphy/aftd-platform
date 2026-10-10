import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumTorque
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumTorqueEq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.torque_apply

Topic: classical_mechanics   Node: 48fb77b84166

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.torque_apply`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The single component of the torque of the simple pendulum is `-m g ℓ sin θ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The single component of the torque of the simple pendulum is `-m g ℓ sin θ`. -/
lemma ClassicalMechanics.SimplePendulum.torque_apply (x : EuclideanSpace ℝ (Fin 1)) :
    S.torque x 0 = -(S.m * S.g * S.ℓ * Real.sin (x 0)) := by
  rw [torque_eq]
  simp
