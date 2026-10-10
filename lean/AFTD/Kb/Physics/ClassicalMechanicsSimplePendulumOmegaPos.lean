import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.ω_pos

Topic: classical_mechanics   Node: cf768c461772

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ω_pos`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The angular frequency of the simple pendulum is positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The angular frequency of the simple pendulum is positive. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.g_pos S.ℓ_pos)
