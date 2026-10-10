import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentOfRat
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.ofRat_toRat

Topic: classical_mechanics   Node: 212fe9b7b8c5

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.ofRat_toRat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.ofRat_toRat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Dimension.Exponent.ofRat_toRat (q : ℚ) : (ofRat q).toRat = q := rfl
