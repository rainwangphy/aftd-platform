import AFTD.Prelude

/-!
# SpeedOfLight

Topic: special_relativity   Node: e64f2c1cd8ce

Provenance: formalization of a published result. Source: Physlib, `SpeedOfLight`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SpeedOfLight.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units. -/
structure SpeedOfLight where
  /-- The underlying value of the speed of light. -/
  val : ℝ
  pos : 0 < val
