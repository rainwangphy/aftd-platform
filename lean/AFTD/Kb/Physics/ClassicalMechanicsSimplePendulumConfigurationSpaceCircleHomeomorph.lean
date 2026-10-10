import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceAngleHomeomorph

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.circleHomeomorph

Topic: classical_mechanics   Node: ab9eb740ae27

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.circleHomeomorph`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The identification of the configuration space with the unit circle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The identification of the configuration space with the unit circle. -/
noncomputable def ClassicalMechanics.SimplePendulum.ConfigurationSpace.circleHomeomorph : ConfigurationSpace ≃ₜ Circle :=
  angleHomeomorph.trans AddCircle.homeomorphCircle'

-- `rfl` proves this because `Real.Angle.toCircle` and `AddCircle.homeomorphCircle'` are the same
-- lift of `Circle.exp`; should that stop holding definitionally, the fallback proof is
-- `Real.Angle.induction_on` with `Real.Angle.toCircle_coe` and
-- `AddCircle.homeomorphCircle'_apply_mk`.
