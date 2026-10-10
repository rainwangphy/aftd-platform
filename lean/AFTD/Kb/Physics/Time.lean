import AFTD.Prelude

/-!
# Time

Topic: classical_mechanics   Node: 3c9a10fa60fb

Provenance: formalization of a published result. Source: Physlib, `Time`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instant in time with a given unit and orientation, but no distinguished origin.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- An instant in time with a given unit and orientation, but no distinguished origin. -/
@[ext]
structure Time where
  /-- The implementation coordinate associated with an instant. -/
  val : ℝ
