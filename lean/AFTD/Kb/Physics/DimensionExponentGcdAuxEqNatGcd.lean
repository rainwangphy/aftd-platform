import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponentGcdAux

/-!
# Dimension.Exponent.gcdAux_eq_nat_gcd

Topic: classical_mechanics   Node: 1595955e9ba7

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.gcdAux_eq_nat_gcd`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.gcdAux_eq_nat_gcd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Dimension.Exponent.gcdAux_eq_nat_gcd (fuel m n : Nat) (m_lt_fuel : m < fuel) :
    gcdAux fuel m n = Nat.gcd m n := by
  induction fuel generalizing m n with
  | zero => omega
  | succ fuel ih =>
      rw [gcdAux, Nat.gcd_def]
      split
      · rfl
      · apply ih; have := Nat.mod_lt n (Nat.zero_lt_of_ne_zero ‹m ≠ 0›); omega
