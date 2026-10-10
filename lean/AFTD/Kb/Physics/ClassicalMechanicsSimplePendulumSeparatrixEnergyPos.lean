import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulum
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumSeparatrixEnergy
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumMNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumLNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumGNeZero
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumOmegaPos
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumInertiaNeZero

/-!
# ClassicalMechanics.SimplePendulum.separatrixEnergy_pos

Topic: classical_mechanics   Node: b3773de72e27

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.separatrixEnergy_pos`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Equilibria.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The separatrix energy of the simple pendulum is positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.SimplePendulum in
open Real InnerProductSpace in
open scoped ContDiff in
variable (S : SimplePendulum) in
/-- The separatrix energy of the simple pendulum is positive. -/
lemma ClassicalMechanics.SimplePendulum.separatrixEnergy_pos : 0 < S.separatrixEnergy :=
  mul_pos two_pos (mul_pos (mul_pos S.m_pos S.g_pos) S.ℓ_pos)
