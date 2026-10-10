import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergyContDiff
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.differentiable_potentialEnergy

Topic: classical_mechanics   Node: db62045b8a0f

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.differentiable_potentialEnergy`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The potential energy of the simple pendulum is a differentiable function of the angle. This is differentiability in the angle; for differentiability in time along a smooth lift of the angle see `potentialEnergy_differentiable`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The potential energy of the simple pendulum is a differentiable function of the angle. This is differentiability in the angle; for differentiability in time along a smooth lift of the angle see `potentialEnergy_differentiable`. -/
@[fun_prop]
lemma ClassicalMechanics.SimplePendulum.differentiable_potentialEnergy : Differentiable ℝ S.potentialEnergy :=
  (S.potentialEnergy_contDiff 1).differentiable one_ne_zero
