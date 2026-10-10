import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngleAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleCircleExp
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstIsManifold

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.cos_angle

Topic: classical_mechanics   Node: ad19a75a5029

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.cos_angle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cosine of a configuration is the cosine of its angle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The cosine of a configuration is the cosine of its angle. -/
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.cos_angle (q : ConfigurationSpace) : q.cos = Real.Angle.cos q.angle := rfl
