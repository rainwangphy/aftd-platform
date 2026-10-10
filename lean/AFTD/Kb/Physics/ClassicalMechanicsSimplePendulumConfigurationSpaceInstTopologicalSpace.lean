import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.instTopologicalSpace

Topic: classical_mechanics   Node: 9ae9e74a26a2

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.instTopologicalSpace`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The topology of the configuration space, induced from `Real.Angle`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The topology of the configuration space, induced from `Real.Angle`. -/
noncomputable instance ClassicalMechanics.SimplePendulum.ConfigurationSpace.instTopologicalSpace : TopologicalSpace ConfigurationSpace :=
  TopologicalSpace.induced angle inferInstance
