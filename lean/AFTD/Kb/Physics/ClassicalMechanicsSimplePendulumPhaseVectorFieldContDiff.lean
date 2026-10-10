import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPhaseVectorField
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.phaseVectorField_contDiff

Topic: classical_mechanics   Node: 6f01275cd8f2

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.phaseVectorField_contDiff`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Solution.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The phase-space vector field of the simple pendulum is smooth: its components are the projection onto the angular velocity and `sin` of the angle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The phase-space vector field of the simple pendulum is smooth: its components are the projection onto the angular velocity and `sin` of the angle. -/
@[fun_prop]
lemma ClassicalMechanics.SimplePendulum.phaseVectorField_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n S.phaseVectorField := by
  unfold phaseVectorField
  fun_prop
