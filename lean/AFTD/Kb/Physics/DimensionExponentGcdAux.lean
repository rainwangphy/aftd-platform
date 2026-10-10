import AFTD.Prelude

/-!
# Dimension.Exponent.gcdAux

Topic: classical_mechanics   Node: 3147f383d9f5

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.gcdAux`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fuel-bounded Euclidean algorithm used to make exponent normalization reducible.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Fuel-bounded Euclidean algorithm used to make exponent normalization reducible. -/
def Dimension.Exponent.gcdAux : Nat → Nat → Nat → Nat
  | 0, _, n => n
  | fuel + 1, m, n => if m = 0 then n else gcdAux fuel (n % m) m
