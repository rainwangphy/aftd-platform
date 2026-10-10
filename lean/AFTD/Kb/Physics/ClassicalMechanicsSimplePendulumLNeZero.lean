import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero

/-!
# ClassicalMechanics.SimplePendulum.ℓ_ne_zero

Topic: classical_mechanics   Node: b8cac92d0aa8

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ℓ_ne_zero`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The length of the rod is not equal to zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The length of the rod is not equal to zero. -/
@[simp]
lemma ClassicalMechanics.SimplePendulum.ℓ_ne_zero : S.ℓ ≠ 0 := S.ℓ_pos.ne'
