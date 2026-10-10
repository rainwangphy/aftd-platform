import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponentGcdAux

/-!
# Dimension.Exponent.gcd

Topic: classical_mechanics   Node: f8c9b860173d

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.gcd`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reducible greatest common divisor used when normalizing an exponent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Reducible greatest common divisor used when normalizing an exponent. -/
def Dimension.Exponent.gcd (m n : Nat) : Nat :=
  gcdAux (m + 1) m n
