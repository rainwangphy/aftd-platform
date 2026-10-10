import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos

/-!
# ClassicalMechanics.SimplePendulum.inertia

Topic: classical_mechanics   Node: 591c35786168

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.inertia`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The moment of inertia of the simple pendulum about its pivot is `I = m ℓ²`, the moment of inertia of a point mass `m` at distance `ℓ` from the axis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The moment of inertia of the simple pendulum about its pivot is `I = m ℓ²`, the moment of inertia of a point mass `m` at distance `ℓ` from the axis. -/
def ClassicalMechanics.SimplePendulum.inertia : ℝ := S.m * S.ℓ ^ 2
