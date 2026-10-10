import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertia
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaSq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.ω_sq_mul_inertia

Topic: classical_mechanics   Node: 3ba1fa1e2475

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ω_sq_mul_inertia`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The square of the angular frequency times the moment of inertia is `m g ℓ`, the coefficient appearing in the potential energy and in the torque. This is the identity by which the mass cancels from the equation of motion.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The square of the angular frequency times the moment of inertia is `m g ℓ`, the coefficient appearing in the potential energy and in the torque. This is the identity by which the mass cancels from the equation of motion. -/
lemma ClassicalMechanics.SimplePendulum.ω_sq_mul_inertia : S.ω ^ 2 * S.inertia = S.m * S.g * S.ℓ := by
  rw [ω_sq, inertia]
  field_simp
