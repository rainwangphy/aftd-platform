import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertia
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos

/-!
# ClassicalMechanics.SimplePendulum.inertia_ne_zero

Topic: classical_mechanics   Node: 848e0c47b263

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.inertia_ne_zero`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The moment of inertia of the simple pendulum is not equal to zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The moment of inertia of the simple pendulum is not equal to zero. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.inertia_ne_zero : S.inertia ≠ 0 := S.inertia_pos.ne'
