import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentEquivRat
import AFTD.Kb.Physics.DimensionExponentMulEquiv
import AFTD.Kb.Physics.DimensionExponentAddEquiv
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv
import AFTD.Kb.Physics.DimensionExponentInstField

/-!
# Dimension.Exponent.ringEquivRat

Topic: classical_mechanics   Node: 25358d3051b4

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.ringEquivRat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The ring equivalence between dimension exponents and rational numbers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The ring equivalence between dimension exponents and rational numbers. -/
def Dimension.Exponent.ringEquivRat : Exponent ≃+* ℚ where
  toEquiv := equivRat
  map_add' := add_equiv
  map_mul' := mul_equiv
