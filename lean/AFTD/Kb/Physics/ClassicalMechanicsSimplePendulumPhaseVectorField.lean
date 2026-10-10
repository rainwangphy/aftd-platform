import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.phaseVectorField

Topic: classical_mechanics   Node: 45f72f477e6c

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.phaseVectorField`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Solution.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The phase-space vector field of the simple pendulum, sending `(θ, θ̇)` to `(θ̇, -ω² sin θ)`. It is the right-hand side of the first-order system on the phase space equivalent to the equation of motion `θ̈ + ω² sin θ = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The phase-space vector field of the simple pendulum, sending `(θ, θ̇)` to `(θ̇, -ω² sin θ)`. It is the right-hand side of the first-order system on the phase space equivalent to the equation of motion `θ̈ + ω² sin θ = 0`. -/
noncomputable def ClassicalMechanics.SimplePendulum.phaseVectorField (p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) :=
  (p.2, -(S.ω ^ 2 * Real.sin (p.1 0)) • EuclideanSpace.single 0 1)
