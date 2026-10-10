import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertia
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumTorque
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumTorqueEq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaSqMulInertia
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.inertia_smul_eq_torque

Topic: classical_mechanics   Node: e1288e8c369c

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.inertia_smul_eq_torque`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Solution.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The pointwise equation of motion in terms of the angular frequency: the moment of inertia times the acceleration `-ω² sin θ` is the torque. This reads the equation of motion back off the second component of the phase-space vector field.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The pointwise equation of motion in terms of the angular frequency: the moment of inertia times the acceleration `-ω² sin θ` is the torque. This reads the equation of motion back off the second component of the phase-space vector field. -/
lemma ClassicalMechanics.SimplePendulum.inertia_smul_eq_torque (x : EuclideanSpace ℝ (Fin 1)) :
    S.inertia • (-(S.ω ^ 2 * Real.sin (x 0)) • EuclideanSpace.single 0 1) = S.torque x := by
  rw [torque_eq, smul_smul, ← neg_smul, ← S.ω_sq_mul_inertia]
  congr
  ring
