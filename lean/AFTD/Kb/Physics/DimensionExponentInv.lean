import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentNum
import AFTD.Kb.Physics.DimensionExponentDen
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub
import AFTD.Kb.Physics.DimensionExponentInstMul

/-!
# Dimension.Exponent.inv

Topic: classical_mechanics   Node: 68f00f1b9022

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.inv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reducible inversion of a dimension exponent, with `0⁻¹ = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Reducible inversion of a dimension exponent, with `0⁻¹ = 0`. -/
def Dimension.Exponent.inv (a : Exponent) : Exponent :=
  if ne_zero : a.toRat ≠ 0 then
    have num_ne_zero : a.num ≠ 0 := ne_zero ∘ Rat.num_eq_zero.mp
    ⟨{ num := a.num.sign * a.den
       den := a.num.natAbs
       den_nz := by exact Nat.ne_of_gt (Int.natAbs_pos.mpr num_ne_zero)
       reduced := by simpa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero num_ne_zero]
         using a.toRat.reduced.symm }⟩
  else a
