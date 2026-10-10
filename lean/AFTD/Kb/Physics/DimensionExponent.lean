import AFTD.Prelude

/-!
# Dimension.Exponent

Topic: classical_mechanics   Node: 79e9c9bcff0a

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A rational dimension exponent with reducible arithmetic.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A rational dimension exponent with reducible arithmetic. -/
structure Dimension.Exponent where
  /-- The rational number represented by the exponent. -/
  toRat : ℚ
deriving DecidableEq

attribute [coe] Dimension.Exponent.toRat
