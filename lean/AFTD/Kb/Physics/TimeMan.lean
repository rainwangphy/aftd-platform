import AFTD.Prelude

/-!
# TimeMan

Topic: classical_mechanics   Node: 829dc03607b5

Provenance: formalization of a published result. Source: Physlib, `TimeMan`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `TimeMan` represents the time manifold. Mathematically `TimeMan` is a manifold diffeomorphic to `ℝ` with an orientation but no additional structure.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `TimeMan` represents the time manifold. Mathematically `TimeMan` is a manifold diffeomorphic to `ℝ` with an orientation but no additional structure. -/
structure TimeMan where
  /-- The choice of a map from `TimeMan` to `ℝ`. -/
  val : ℝ
