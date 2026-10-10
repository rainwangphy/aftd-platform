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
# ClassicalMechanics.SimplePendulum.potentialEnergy_le

Topic: classical_mechanics   Node: 047a67a8abf2

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.potentialEnergy_le`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The potential energy of the simple pendulum is at most `2 m g ℓ`, its value at the top of the swing.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The potential energy of the simple pendulum is at most `2 m g ℓ`, its value at the top of the swing. -/
lemma ClassicalMechanics.SimplePendulum.potentialEnergy_le (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x ≤ 2 * (S.m * S.g * S.ℓ) := by
  have hc : 0 < S.m * S.g * S.ℓ := mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos
  have h : 1 - Real.cos (x 0) ≤ 2 := by
    have := Real.neg_one_le_cos (x 0)
    linarith
  calc S.potentialEnergy x = S.m * S.g * S.ℓ * (1 - Real.cos (x 0)) := S.potentialEnergy_eq x
    _ ≤ S.m * S.g * S.ℓ * 2 := mul_le_mul_of_nonneg_left h hc.le
    _ = 2 * (S.m * S.g * S.ℓ) := by ring
