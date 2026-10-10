import AFTD.Prelude

/-!
# ClassicalMechanics.SlidingPendulum.ConfigurationSpace

Topic: classical_mechanics   Node: a166653bc9e9

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SlidingPendulum.ConfigurationSpace`. Lean proof by Shlok Vaibhav Singh, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SlidingPendulum.lean (Copyright (c) 2025 Shlok Vaibhav Singh. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The configuration space of the sliding pendulum system. The generalized coordinates are the horizontal position of the support mass and the angle that the string makes with the vertical.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The configuration space of the sliding pendulum system. The generalized coordinates are the horizontal position of the support mass and the angle that the string makes with the vertical. -/
structure ClassicalMechanics.SlidingPendulum.ConfigurationSpace where
  /-- The horizontal position `x₁` of the support mass. -/
  supportPosition : ℝ
  /-- The angle `φ` that the string makes with the vertical. -/
  angle : Real.Angle
