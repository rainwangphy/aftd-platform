import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.equivRat

Topic: classical_mechanics   Node: f27f44957edb

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.equivRat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `Exponent` and the rational numbers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The equivalence between `Exponent` and the rational numbers. -/
def Dimension.Exponent.equivRat : Exponent ≃ ℚ :=
  Equiv.mk Exponent.toRat Exponent.mk Eq.refl Eq.refl
