import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.den

Topic: classical_mechanics   Node: f72684bbd457

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.den`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normalized denominator of an exponent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The normalized denominator of an exponent. -/
@[reducible] def Dimension.Exponent.den (x : Exponent) : Nat :=
  x.toRat.den
