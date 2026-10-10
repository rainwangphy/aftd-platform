import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle_ofCircle

Topic: classical_mechanics   Node: 495d1c93cadf

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle_ofCircle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The point of the unit circle of the configuration attached to a point of the unit circle is that point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The point of the unit circle of the configuration attached to a point of the unit circle is that point. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle_ofCircle (z : Circle) : (ofCircle z).toCircle = z :=
  circleHomeomorph.apply_symm_apply z
