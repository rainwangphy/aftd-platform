import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofCircle_toCircle

Topic: classical_mechanics   Node: 5e899ed2ad75

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofCircle_toCircle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The configuration attached to the point of the unit circle of a configuration is that configuration.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The configuration attached to the point of the unit circle of a configuration is that configuration. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofCircle_toCircle (q : ConfigurationSpace) : ofCircle q.toCircle = q :=
  circleHomeomorph.symm_apply_apply q
