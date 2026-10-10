import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPotentialEnergyEq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.potentialEnergy_eq_zero_iff

Topic: classical_mechanics   Node: c33398306c2b

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.potentialEnergy_eq_zero_iff`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The potential energy of the simple pendulum vanishes exactly when the cosine of the angle is equal to `1`, that is exactly at the bottom of the swing.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The potential energy of the simple pendulum vanishes exactly when the cosine of the angle is equal to `1`, that is exactly at the bottom of the swing. -/
lemma ClassicalMechanics.SimplePendulum.potentialEnergy_eq_zero_iff (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = 0 ↔ Real.cos (x 0) = 1 := by
  have hc : S.m * S.g * S.ℓ ≠ 0 := (mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos).ne'
  rw [potentialEnergy_eq, mul_eq_zero, or_iff_right hc, sub_eq_zero, eq_comm]
