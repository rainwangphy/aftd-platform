import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum

/-!
# ClassicalMechanics.SimplePendulum.m_ne_zero

Topic: classical_mechanics   Node: 7390fbbd0aa0

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.m_ne_zero`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The mass of the bob is not equal to zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The mass of the bob is not equal to zero. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.m_ne_zero : S.m ≠ 0 := S.m_pos.ne'
