import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.instChartedSpace

Topic: classical_mechanics   Node: 63422115b9e3

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.instChartedSpace`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The charts of the configuration space: the identification with the unit circle followed by a chart of the circle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The charts of the configuration space: the identification with the unit circle followed by a chart of the circle. -/
noncomputable instance ClassicalMechanics.SimplePendulum.ConfigurationSpace.instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace where
  atlas := {circleHomeomorph.toOpenPartialHomeomorph.trans e |
    e ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle}
  chartAt q := circleHomeomorph.toOpenPartialHomeomorph.trans
    (chartAt (EuclideanSpace ℝ (Fin 1)) (circleHomeomorph q))
  mem_chart_source q := by simp
  chart_mem_atlas q := ⟨_, chart_mem_atlas _ _, rfl⟩
