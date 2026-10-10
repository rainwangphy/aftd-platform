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
# ClassicalMechanics.SimplePendulum.torque_add_int_mul_two_pi

Topic: classical_mechanics   Node: 760cde1ae56c

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.torque_add_int_mul_two_pi`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/LiftInvariance.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The torque of the simple pendulum is invariant under shifting the angle by a whole number of turns.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The torque of the simple pendulum is invariant under shifting the angle by a whole number of turns. -/
lemma ClassicalMechanics.SimplePendulum.torque_add_int_mul_two_pi (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.torque (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) = S.torque x := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [torque_eq, torque_eq, h0, Real.sin_add_int_mul_two_pi]
