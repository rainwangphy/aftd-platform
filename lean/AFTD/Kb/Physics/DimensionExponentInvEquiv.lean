import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentEquivRat
import AFTD.Kb.Physics.DimensionExponentInv
import AFTD.Kb.Physics.DimensionExponentNum
import AFTD.Kb.Physics.DimensionExponentDen
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul
import AFTD.Kb.Physics.DimensionExponentInstInv

/-!
# Dimension.Exponent.inv_equiv

Topic: classical_mechanics   Node: 3d922f93b125

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.inv_equiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.inv_equiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Dimension.Exponent.inv_equiv (a : Exponent) : equivRat (inv a) = (equivRat a)⁻¹ := by
  by_cases ne_zero : a.toRat ≠ 0
  · apply Rat.ext <;> simp [inv, ne_zero, equivRat, Rat.num_inv, Rat.den_inv]
  · push Not at ne_zero
    apply Rat.ext <;> simp [inv, ne_zero, equivRat]
