import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.angleEquiv

Topic: classical_mechanics   Node: 1e4badc5a2cf

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.angleEquiv`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The identification of the configuration space with `Real.Angle`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The identification of the configuration space with `Real.Angle`. -/
noncomputable def ClassicalMechanics.SimplePendulum.ConfigurationSpace.angleEquiv : ConfigurationSpace ≃ Real.Angle where
  toFun := angle
  invFun φ := ⟨φ⟩
  left_inv q := by cases q; rfl
  right_inv φ := rfl
