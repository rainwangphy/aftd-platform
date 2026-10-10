import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstIsManifold
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceContinuousOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceChartAtEq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorphApply
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceExt
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfAngleAngle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleCircleExp
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.contMDiff_ofAngle

Topic: classical_mechanics   Node: 14fd8125d8d3

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.contMDiff_ofAngle`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The angular lift is analytic: read in the charts pulled back from the circle it is `Circle.exp`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The angular lift is analytic: read in the charts pulled back from the circle it is `Circle.exp`. -/
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.contMDiff_ofAngle : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ω' ofAngle := by
  rw [contMDiff_iff]
  refine ⟨continuous_ofAngle, fun x y => ?_⟩
  have h := (contMDiff_iff.mp (contMDiff_circleExp (m := ω'))).2 x y.toCircle
  -- Two goals remain: the map read in the charts, and the domain on which it is read.
  convert h using 2
  · rfl
  · ext θ
    simp [chartAt_eq, circleHomeomorph_apply, toCircle_ofAngle]
