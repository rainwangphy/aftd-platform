import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentDen
import AFTD.Kb.Physics.DimensionExponentNormalize
import AFTD.Kb.Physics.DimensionExponentNum
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.add

Topic: classical_mechanics   Node: 4444a5656e3e

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.add`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reducible addition of dimension exponents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Reducible addition of dimension exponents. -/
def Dimension.Exponent.add (a b : Exponent) : Exponent :=
  normalize (a.num * b.den + b.num * a.den) (a.den * b.den)
    (Nat.mul_ne_zero a.toRat.den_nz b.toRat.den_nz)
