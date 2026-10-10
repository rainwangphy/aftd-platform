import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentInstLinearOrder
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionExponentCoeInj
import AFTD.Kb.Physics.DimensionExponentCoeZero
import AFTD.Kb.Physics.DimensionExponentCoeOne
import AFTD.Kb.Physics.DimensionExponentCoeOfNat
import AFTD.Kb.Physics.DimensionExponentCoeAdd
import AFTD.Kb.Physics.DimensionExponentCoeSub
import AFTD.Kb.Physics.DimensionExponentCoeNeg
import AFTD.Kb.Physics.DimensionExponentCoeMul
import AFTD.Kb.Physics.DimensionExponentCoeInv
import AFTD.Kb.Physics.DimensionExponentCoeDiv
import AFTD.Kb.Physics.DimensionExponentCoeLeCoe
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv
import AFTD.Kb.Physics.DimensionExponentInstField
import AFTD.Kb.Physics.DimensionExponentInstCoeRat
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Dimension.Exponent.coe_lt_coe

Topic: classical_mechanics   Node: 6ee1b426bf19

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.coe_lt_coe`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.coe_lt_coe
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp, norm_cast]
lemma Dimension.Exponent.coe_lt_coe {a b : Exponent} : (a : ℚ) < b ↔ a < b := Iff.rfl
