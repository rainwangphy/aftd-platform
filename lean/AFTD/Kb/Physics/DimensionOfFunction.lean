import AFTD.Prelude
import AFTD.Kb.Physics.DimensionBasis
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.Dimension
import AFTD.Kb.Physics.DimensionExponentInstAdd
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
import AFTD.Kb.Physics.DimensionExponentCoeLtCoe
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv
import AFTD.Kb.Physics.DimensionExponentInstField
import AFTD.Kb.Physics.DimensionExponentInstCoeRat
import AFTD.Kb.Physics.DimensionExponentInstLinearOrder
import AFTD.Kb.Physics.DimensionExponentInstIsStrictOrderedRing
import AFTD.Kb.Physics.DimensionExponentInstCharZero

/-!
# Dimension.ofFunction

Topic: classical_mechanics   Node: 41ac32af9cec

Provenance: formalization of a published result. Source: Physlib, `Dimension.ofFunction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Dimension.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Construct a dimension from an exponent function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Dimension in
variable {B : Type} [DimensionBasis B] in
/-- Construct a dimension from an exponent function. -/
def Dimension.ofFunction (f : B → Exponent) : Dimension B :=
  ⟨DimensionBasis.exponentEquiv.symm f⟩
