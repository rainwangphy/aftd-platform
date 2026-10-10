import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmega
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaSq
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.SimplePendulum.inverse_ω_sq

Topic: classical_mechanics   Node: ea871069bb2e

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.inverse_ω_sq`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inverse of the square of the angular frequency of the simple pendulum is `ℓ/g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The inverse of the square of the angular frequency of the simple pendulum is `ℓ/g`. -/
lemma ClassicalMechanics.SimplePendulum.inverse_ω_sq : (S.ω ^ 2)⁻¹ = S.ℓ / S.g := by rw [ω_sq, inv_div]
