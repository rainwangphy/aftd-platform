import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentAdd
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.instAdd

Topic: classical_mechanics   Node: 85cca6ed5259

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.instAdd`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.instAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Dimension.Exponent.instAdd : Add Exponent := Add.mk add
