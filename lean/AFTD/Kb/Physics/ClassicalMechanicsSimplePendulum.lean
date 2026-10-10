import AFTD.Prelude

/-!
# ClassicalMechanics.SimplePendulum

Topic: classical_mechanics   Node: 0c432924d0ee

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The simple gravity pendulum is specified by the mass `m` of its bob, the length `ℓ` of its rod, and the gravitational acceleration `g`. All three are assumed to be positive. The configuration of the pendulum is the angle of the rod from the downward vertical.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real InnerProductSpace in
/-- The simple gravity pendulum is specified by the mass `m` of its bob, the length `ℓ` of its rod, and the gravitational acceleration `g`. All three are assumed to be positive. The configuration of the pendulum is the angle of the rod from the downward vertical. -/
structure ClassicalMechanics.SimplePendulum where
  /-- The mass of the bob. -/
  m : ℝ
  /-- The length of the massless rod. -/
  ℓ : ℝ
  /-- The gravitational acceleration. -/
  g : ℝ
  m_pos : 0 < m
  ℓ_pos : 0 < ℓ
  g_pos : 0 < g
