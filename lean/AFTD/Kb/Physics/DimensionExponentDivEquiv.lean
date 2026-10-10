import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentEquivRat
import AFTD.Kb.Physics.DimensionExponentDiv
import AFTD.Kb.Physics.DimensionExponentMul
import AFTD.Kb.Physics.DimensionExponentInv
import AFTD.Kb.Physics.DimensionExponentMulEquiv
import AFTD.Kb.Physics.DimensionExponentInvEquiv
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv

/-!
# Dimension.Exponent.div_equiv

Topic: classical_mechanics   Node: ff690389b04b

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.div_equiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.div_equiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Dimension.Exponent.div_equiv (a b : Exponent) : equivRat (div a b) = equivRat a / equivRat b := by
  rw [div, mul_equiv, inv_equiv, div_eq_mul_inv]
