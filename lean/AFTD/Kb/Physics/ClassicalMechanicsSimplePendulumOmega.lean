import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero

/-!
# ClassicalMechanics.SimplePendulum.ω

Topic: classical_mechanics   Node: 331c93973ac4

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ω`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The angular frequency of the simple pendulum, `ω`, is defined as `√(g/ℓ)`. It is the angular frequency of the small oscillations of the pendulum about the bottom of its swing.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
open Real InnerProductSpace in
variable (S : SimplePendulum) in
/-- The angular frequency of the simple pendulum, `ω`, is defined as `√(g/ℓ)`. It is the angular frequency of the small oscillations of the pendulum about the bottom of its swing. -/
noncomputable def ClassicalMechanics.SimplePendulum.ω : ℝ := √(S.g / S.ℓ)
