import AFTD.Prelude

/-!
# LengthUnit

Topic: classical_mechanics   Node: 8e07d2153821

Provenance: formalization of a published result. Source: Physlib, `LengthUnit`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/LengthUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length. -/
structure LengthUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val
