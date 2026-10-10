import AFTD.Prelude

/-!
# PositiveRealUnitCore

Topic: classical_mechanics   Node: 8dcd9e9bce9f

Provenance: formalization of a published result. Source: Physlib, `PositiveRealUnitCore`. Lean proof by Joseph Tooby-Smith, Hirotaka Monya, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/PositiveRealUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Common representation API for unit types whose magnitude is a positive real.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- Common representation API for unit types whose magnitude is a positive real. -/
class PositiveRealUnitCore (U : Type) where
  /-- The underlying real magnitude of a unit. -/
  val : U → ℝ
  /-- Every unit has a strictly positive magnitude. -/
  pos : ∀ x, 0 < val x
  /-- Construct a unit from a positive real magnitude. -/
  ofVal : (r : ℝ) → 0 < r → U
  /-- Construction preserves the supplied magnitude. -/
  val_ofVal : ∀ r hr, val (ofVal r hr) = r
  /-- Reconstructing a unit from its magnitude returns that unit. -/
  ofVal_val : ∀ x, ofVal (val x) (pos x) = x
