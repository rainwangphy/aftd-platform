import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.num

Topic: classical_mechanics   Node: b9f1a20e972b

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.num`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normalized numerator of an exponent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The normalized numerator of an exponent. -/
@[reducible] def Dimension.Exponent.num (x : Exponent) : Int :=
  x.toRat.num
