import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergyEq
import AFTD.Kb.Physics.GradientAddConst
import AFTD.Kb.Physics.GradientConstMul
import AFTD.Kb.Physics.GradientCompCoord
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.gradient_potentialEnergy

Topic: classical_mechanics   Node: 93a91ff40ab6

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.gradient_potentialEnergy`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of the potential energy of the simple pendulum is `m g ℓ sin θ` times the unit vector of the angular coordinate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The gradient of the potential energy of the simple pendulum is `m g ℓ sin θ` times the unit vector of the angular coordinate. -/
lemma ClassicalMechanics.SimplePendulum.gradient_potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) :
    gradient S.potentialEnergy x =
      (S.m * S.g * S.ℓ * Real.sin (x 0)) • EuclideanSpace.single 0 1 := by
  have hcos : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 1) => Real.cos (y 0)) x := by
    fun_prop
  have h : S.potentialEnergy = fun y : EuclideanSpace ℝ (Fin 1) =>
      -(S.m * S.g * S.ℓ) * Real.cos (y 0) + S.m * S.g * S.ℓ := by
    funext y
    rw [potentialEnergy_eq]
    ring
  rw [h, gradient_add_const, gradient_const_mul _ hcos,
    gradient_comp_coord 0 x (Real.hasDerivAt_cos (x 0))]
  module
