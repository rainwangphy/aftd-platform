import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.torque

Topic: classical_mechanics   Node: dc4618789045

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.torque`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The generalized force of the simple pendulum conjugate to the angle, that is the torque about the pivot, is minus the gradient of the potential energy, `τ = -∂V/∂θ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The generalized force of the simple pendulum conjugate to the angle, that is the torque about the pivot, is minus the gradient of the potential energy, `τ = -∂V/∂θ`. -/
noncomputable def ClassicalMechanics.SimplePendulum.torque (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  -gradient S.potentialEnergy x
