import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngleAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstIsManifold

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle_ofAngle

Topic: classical_mechanics   Node: e0143e7714f1

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle_ofAngle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The configuration at angle `θ` corresponds to the point `e^{iθ}` of the unit circle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The configuration at angle `θ` corresponds to the point `e^{iθ}` of the unit circle. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle_ofAngle (θ : ℝ) : (ofAngle θ).toCircle = Circle.exp θ := Real.Angle.toCircle_coe θ
