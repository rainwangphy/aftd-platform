import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent

/-!
# Dimension.instReprExponent

Topic: classical_mechanics   Node: 0c96bd13047e

Provenance: formalization of a published result. Source: Physlib, `Dimension.instReprExponent`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.instReprExponent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Dimension.instReprExponent : Repr Exponent where
  reprPrec x := reprPrec x.toRat
