import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentEquivRat
import AFTD.Kb.Physics.DimensionExponentAdd
import AFTD.Kb.Physics.DimensionExponentNormalizeToRat
import AFTD.Kb.Physics.DimensionExponentNum
import AFTD.Kb.Physics.DimensionExponentDen
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd

/-!
# Dimension.Exponent.add_equiv

Topic: classical_mechanics   Node: ccf5babecb81

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.add_equiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.add_equiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Dimension.Exponent.add_equiv (a b : Exponent) : equivRat (add a b) = equivRat a + equivRat b := by
  rw [Rat.add_def]
  exact normalize_toRat _ _ _
