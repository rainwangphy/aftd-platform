import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceAngleEquiv
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.angleHomeomorph

Topic: classical_mechanics   Node: 8db5c111af1c

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.angleHomeomorph`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The identification with `Real.Angle` as a homeomorphism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The identification with `Real.Angle` as a homeomorphism. -/
noncomputable def ClassicalMechanics.SimplePendulum.ConfigurationSpace.angleHomeomorph : ConfigurationSpace ≃ₜ Real.Angle where
  toEquiv := angleEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id
