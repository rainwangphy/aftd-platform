import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentNormalize
import AFTD.Kb.Physics.DimensionExponentGcd
import AFTD.Kb.Physics.DimensionExponentGcdEqNatGcd
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.normalize_toRat

Topic: classical_mechanics   Node: 77bba1314e07

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.normalize_toRat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.normalize_toRat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Dimension.Exponent.normalize_toRat (num : Int) (den : Nat) (den_ne_zero : den ≠ 0) :
    (normalize num den den_ne_zero).toRat = Rat.normalize num den den_ne_zero := by
  unfold normalize Rat.normalize
  simp only [gcd_eq_nat_gcd]
