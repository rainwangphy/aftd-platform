import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstIsManifold

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofAngle_angle

Topic: classical_mechanics   Node: 5b1f9aa8e8f4

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofAngle_angle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The angle of the configuration at angle `θ` is `θ` modulo `2π`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The angle of the configuration at angle `θ` is `θ` modulo `2π`. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofAngle_angle (θ : ℝ) : (ofAngle θ).angle = θ := rfl
