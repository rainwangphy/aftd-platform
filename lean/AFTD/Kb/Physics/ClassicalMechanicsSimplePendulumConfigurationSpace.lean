import AFTD.Prelude

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace

Topic: classical_mechanics   Node: 24931c4c4172

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The configuration space of the planar simple pendulum: the angle of the rod from the downward vertical, modulo `2π`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The configuration space of the planar simple pendulum: the angle of the rod from the downward vertical, modulo `2π`. -/
structure ClassicalMechanics.SimplePendulum.ConfigurationSpace where
  /-- The angle of the rod from the downward vertical, modulo `2π`. -/
  angle : Real.Angle
