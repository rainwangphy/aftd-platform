import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentAdd
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd

/-!
# Dimension.Exponent.sub

Topic: classical_mechanics   Node: 138ac0b8d08e

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.sub`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reducible subtraction of dimension exponents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Reducible subtraction of dimension exponents. -/
def Dimension.Exponent.sub (a b : Exponent) : Exponent :=
  add a ⟨-b.toRat⟩
