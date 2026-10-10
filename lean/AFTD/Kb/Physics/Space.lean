import AFTD.Prelude

/-!
# Space

Topic: classical_mechanics   Node: 13860c9420cd

Provenance: formalization of a published result. Source: Physlib, `Space`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `Space d` is the world-volume which corresponds to `d` dimensional (flat) Euclidean space with a given (but arbitrary) choice of length unit, and a given (but arbitrary) choice of zero. The default value of `d` is `3`. Thus `Space = Space 3`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `Space d` is the world-volume which corresponds to `d` dimensional (flat) Euclidean space with a given (but arbitrary) choice of length unit, and a given (but arbitrary) choice of zero. The default value of `d` is `3`. Thus `Space = Space 3` -/
structure Space (d : ℕ := 3) where
  /-- The underlying map `Fin d → ℝ` associated with a point in `Space`. -/
  val : Fin d → ℝ
