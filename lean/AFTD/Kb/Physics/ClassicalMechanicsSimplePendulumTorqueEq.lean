import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumTorque
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGradientPotentialEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.torque_eq

Topic: classical_mechanics   Node: e1defd505fe7

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.torque_eq`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The torque of the simple pendulum is `-m g ℓ sin θ` times the unit vector of the angular coordinate. It is restoring near the bottom of the swing: for `|θ| < π` it opposes the displacement, and it vanishes both at the bottom and at the inverted position.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The torque of the simple pendulum is `-m g ℓ sin θ` times the unit vector of the angular coordinate. It is restoring near the bottom of the swing: for `|θ| < π` it opposes the displacement, and it vanishes both at the bottom and at the inverted position. -/
lemma ClassicalMechanics.SimplePendulum.torque_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.torque x = -((S.m * S.g * S.ℓ * Real.sin (x 0)) • EuclideanSpace.single 0 1) := by
  rw [torque, gradient_potentialEnergy]
