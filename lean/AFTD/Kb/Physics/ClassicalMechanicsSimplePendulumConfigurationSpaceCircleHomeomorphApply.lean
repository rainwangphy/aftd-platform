import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.circleHomeomorph_apply

Topic: classical_mechanics   Node: 60fd99ac6eea

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.circleHomeomorph_apply`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The identification with the unit circle is given by `ConfigurationSpace.toCircle`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The identification with the unit circle is given by `ConfigurationSpace.toCircle`. -/
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.circleHomeomorph_apply (q : ConfigurationSpace) : circleHomeomorph q = q.toCircle := rfl
