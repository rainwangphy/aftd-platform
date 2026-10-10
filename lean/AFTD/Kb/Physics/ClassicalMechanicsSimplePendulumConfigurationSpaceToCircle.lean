import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle

Topic: classical_mechanics   Node: dad03a3a7f2f

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The point of the unit circle `e^{iθ}` corresponding to a configuration at angle `θ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The point of the unit circle `e^{iθ}` corresponding to a configuration at angle `θ`. -/
noncomputable def ClassicalMechanics.SimplePendulum.ConfigurationSpace.toCircle (q : ConfigurationSpace) : Circle := q.angle.toCircle
