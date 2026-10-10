import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumPhaseVectorField
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.phaseVectorField_lipschitz

Topic: classical_mechanics   Node: 6c4b335ef75d

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.phaseVectorField_lipschitz`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Solution.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The phase-space vector field of the simple pendulum is globally Lipschitz, with constant `1 + ω²`: the first component is the projection onto the angular velocity, and the second is `-ω²` times `sin` of the angle, and `sin` is Lipschitz with constant one.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The phase-space vector field of the simple pendulum is globally Lipschitz, with constant `1 + ω²`: the first component is the projection onto the angular velocity, and the second is `-ω²` times `sin` of the angle, and `sin` is Lipschitz with constant one. -/
lemma ClassicalMechanics.SimplePendulum.phaseVectorField_lipschitz :
    LipschitzWith (Real.toNNReal (1 + S.ω ^ 2)) S.phaseVectorField := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, add_mul, one_mul]
  apply max_le _ _
  · apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact le_max_right _ _
  · apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply le_trans (dist_pair_smul _ _ _)
    rw [dist_neg_neg, dist_eq_norm, norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _),
      mul_assoc, mul_le_mul_iff_right₀ (pow_succ_pos S.ω_pos _), dist_zero_right, PiLp.norm_single,
      norm_one, mul_one]
    apply le_trans _ (le_max_left _ _)
    apply le_trans (Real.abs_sin_sub_sin_le _ _)
    rw [dist_eq_norm, ← Real.norm_eq_abs, ← PiLp.sub_apply]
    exact PiLp.norm_apply_le _ _
