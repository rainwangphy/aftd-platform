import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv
import AFTD.Kb.Physics.DimensionExponentInstDiv
import AFTD.Kb.Physics.DimensionExponentInstField

/-!
# Dimension.Exponent.instCoeRat

Topic: classical_mechanics   Node: e894a92b0bf3

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.instCoeRat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Regard a dimension exponent as a rational number.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Regard a dimension exponent as a rational number. -/
instance Dimension.Exponent.instCoeRat : Coe Exponent ℚ := ⟨Exponent.toRat⟩
