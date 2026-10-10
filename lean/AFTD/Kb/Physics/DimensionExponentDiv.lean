import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentMul
import AFTD.Kb.Physics.DimensionExponentInv
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv

/-!
# Dimension.Exponent.div

Topic: classical_mechanics   Node: a5d4df4f8503

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.div`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reducible division of dimension exponents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Reducible division of dimension exponents. -/
def Dimension.Exponent.div (a b : Exponent) : Exponent :=
  mul a (inv b)
