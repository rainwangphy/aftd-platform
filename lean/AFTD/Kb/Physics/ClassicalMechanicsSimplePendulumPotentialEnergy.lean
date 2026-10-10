import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.potentialEnergy

Topic: classical_mechanics   Node: 30a30c716db7

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.potentialEnergy`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The potential energy of the simple pendulum at the angle `x` is `m g ℓ (1 - cos (x 0))`, the work done against gravity in raising the bob from the bottom of the swing. It is normalized to vanish at the bottom.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The potential energy of the simple pendulum at the angle `x` is `m g ℓ (1 - cos (x 0))`, the work done against gravity in raising the bob from the bottom of the swing. It is normalized to vanish at the bottom. -/
noncomputable def ClassicalMechanics.SimplePendulum.potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  S.m * S.g * S.ℓ * (1 - Real.cos (x 0))
