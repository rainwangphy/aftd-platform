import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.ext

Topic: classical_mechanics   Node: 58a264c92f81

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.ext`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two configurations are equal precisely when their angles are equal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- Two configurations are equal precisely when their angles are equal. -/
@[ext]
lemma ClassicalMechanics.SimplePendulum.ConfigurationSpace.ext {p q : ConfigurationSpace} (h : p.angle = q.angle) : p = q := by
  cases p; cases q; cases h; rfl
