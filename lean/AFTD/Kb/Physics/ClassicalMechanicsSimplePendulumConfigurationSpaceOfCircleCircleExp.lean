import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngleAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstIsManifold

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofCircle_circleExp

Topic: classical_mechanics   Node: 73b8a199b781

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofCircle_circleExp`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The configuration of a point `e^{iθ}` of the unit circle is `ofAngle θ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The configuration of a point `e^{iθ}` of the unit circle is `ofAngle θ`. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofCircle_circleExp (θ : ℝ) : ofCircle (Circle.exp θ) = ofAngle θ := by
  rw [← toCircle_ofAngle, ofCircle_toCircle]
