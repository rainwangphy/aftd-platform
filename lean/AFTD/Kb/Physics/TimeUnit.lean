import AFTD.Prelude

/-!
# TimeUnit

Topic: classical_mechanics   Node: a270566cdbfc

Provenance: formalization of a published result. Source: Physlib, `TimeUnit`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choices of translationally-invariant metrics on the time manifold. Such a choice corresponds to a choice of units for time.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The choices of translationally-invariant metrics on the time manifold. Such a choice corresponds to a choice of units for time. -/
structure TimeUnit : Type where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val
