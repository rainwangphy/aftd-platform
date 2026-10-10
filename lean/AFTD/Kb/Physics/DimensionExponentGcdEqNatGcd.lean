import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponentGcd
import AFTD.Kb.Physics.DimensionExponentGcdAuxEqNatGcd

/-!
# Dimension.Exponent.gcd_eq_nat_gcd

Topic: classical_mechanics   Node: 2ca88d91eb70

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.gcd_eq_nat_gcd`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The reducible exponent GCD agrees with `Nat.gcd`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The reducible exponent GCD agrees with `Nat.gcd`. -/
lemma Dimension.Exponent.gcd_eq_nat_gcd (m n : Nat) : gcd m n = Nat.gcd m n := by
  exact gcdAux_eq_nat_gcd (m + 1) m n (Nat.lt_add_one m)
