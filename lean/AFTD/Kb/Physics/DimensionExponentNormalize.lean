import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponentGcd
import AFTD.Kb.Physics.DimensionExponentGcdEqNatGcd
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.normalize

Topic: classical_mechanics   Node: 08408947c0e8

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.normalize`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Construct an exponent by normalizing a numerator and a nonzero denominator.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Construct an exponent by normalizing a numerator and a nonzero denominator. -/
def Dimension.Exponent.normalize (num : Int) (den : Nat) (den_ne_zero : den ≠ 0) : Exponent :=
  let g := gcd num.natAbs den
  let g_eq : g = num.natAbs.gcd den := gcd_eq_nat_gcd num.natAbs den
  ⟨Rat.maybeNormalize num den g
    (Rat.normalize.dvd_num g_eq)
    (Rat.normalize.dvd_den g_eq)
    (Rat.normalize.den_nz den_ne_zero g_eq)
    (Rat.normalize.reduced den_ne_zero g_eq)⟩
