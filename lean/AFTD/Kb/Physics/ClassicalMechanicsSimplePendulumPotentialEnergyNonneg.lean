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
# ClassicalMechanics.SimplePendulum.potentialEnergy_nonneg

Topic: classical_mechanics   Node: 6bd0ce67682e

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.potentialEnergy_nonneg`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The potential energy of the simple pendulum is non-negative, the bottom of the swing being the lowest point of the circle on which the bob moves.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
open scoped ContDiff in
/-- The potential energy of the simple pendulum is non-negative, the bottom of the swing being the lowest point of the circle on which the bob moves. -/
lemma ClassicalMechanics.SimplePendulum.potentialEnergy_nonneg (x : EuclideanSpace ℝ (Fin 1)) : 0 ≤ S.potentialEnergy x := by
  have hc : 0 < S.m * S.g * S.ℓ := mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos
  have h : (0 : ℝ) ≤ 1 - Real.cos (x 0) := by
    have := Real.cos_le_one (x 0)
    linarith
  rw [potentialEnergy_eq]
  exact mul_nonneg hc.le h
