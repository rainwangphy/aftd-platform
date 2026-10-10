import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.separatrixEnergy

Topic: classical_mechanics   Node: ea123d89e8a3

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.separatrixEnergy`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Equilibria.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The separatrix energy of the simple pendulum is `2 m g ℓ`, the energy of the inverted equilibrium. It is the threshold separating the two regimes of the motion, libration below it and rotation above it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
open Real InnerProductSpace in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The separatrix energy of the simple pendulum is `2 m g ℓ`, the energy of the inverted equilibrium. It is the threshold separating the two regimes of the motion, libration below it and rotation above it. -/
def ClassicalMechanics.SimplePendulum.separatrixEnergy : ℝ := 2 * (S.m * S.g * S.ℓ)
