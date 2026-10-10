import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceChartAtEq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.chartAt_source

Topic: classical_mechanics   Node: 749557fefae4

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.chartAt_source`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The domain of the chart at a configuration is the preimage under the identification with the unit circle of the domain of the chart of the circle at the corresponding point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The domain of the chart at a configuration is the preimage under the identification with the unit circle of the domain of the chart of the circle at the corresponding point. -/
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.chartAt_source (q : ConfigurationSpace) :
    (chartAt (EuclideanSpace ℝ (Fin 1)) q).source =
      circleHomeomorph ⁻¹' (chartAt (EuclideanSpace ℝ (Fin 1)) q.toCircle).source := by
  rw [chartAt_eq, OpenPartialHomeomorph.trans_source]
  simp
