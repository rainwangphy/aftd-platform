import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceExt
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngleAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstIsManifold

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofAngle_eq_iff

Topic: classical_mechanics   Node: 21bd80b758c9

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofAngle_eq_iff`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two angles describe the same configuration exactly when they differ by a whole number of turns.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- Two angles describe the same configuration exactly when they differ by a whole number of turns. -/
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.ofAngle_eq_iff (θ₁ θ₂ : ℝ) :
    ofAngle θ₁ = ofAngle θ₂ ↔ ∃ n : ℤ, θ₂ = θ₁ + n * (2 * Real.pi) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ :=
      Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (congrArg ConfigurationSpace.angle h)
    exact ⟨-k, by push_cast; linarith⟩
  · rintro ⟨n, rfl⟩
    exact ConfigurationSpace.ext
      (Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr ⟨-n, by push_cast; ring⟩)
