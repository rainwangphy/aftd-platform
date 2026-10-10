import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentEquivRat
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv
import AFTD.Kb.Physics.DimensionExponentAddEquiv
import AFTD.Kb.Physics.DimensionExponentMulEquiv
import AFTD.Kb.Physics.DimensionExponentSubEquiv
import AFTD.Kb.Physics.DimensionExponentInvEquiv
import AFTD.Kb.Physics.DimensionExponentDivEquiv
import AFTD.Kb.Physics.DimensionExponentAdd
import AFTD.Kb.Physics.DimensionExponentDiv
import AFTD.Kb.Physics.DimensionExponentInv
import AFTD.Kb.Physics.DimensionExponentMul
import AFTD.Kb.Physics.DimensionExponentSub
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.instField

Topic: classical_mechanics   Node: f5d98fac5d3a

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.instField`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.instField
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Dimension.Exponent.instField : Field Exponent := by
  letI := equivRat.field
  apply equivRat.injective.field
  · rfl
  · rfl
  all_goals intros
  case add => apply add_equiv
  case sub => apply sub_equiv
  case inv => apply inv_equiv
  case mul => apply mul_equiv
  case div => apply div_equiv
  all_goals rfl
