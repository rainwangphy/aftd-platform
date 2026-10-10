import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionExponentEquivRat
import AFTD.Kb.Physics.DimensionExponentSub
import AFTD.Kb.Physics.DimensionExponentAdd
import AFTD.Kb.Physics.DimensionExponentAddEquiv
import AFTD.Kb.Physics.DimensionExponentOfRatToRat
import AFTD.Kb.Physics.DimensionInstReprExponent
import AFTD.Kb.Physics.DimensionExponentInstAdd
import AFTD.Kb.Physics.DimensionExponentInstSub

/-!
# Dimension.Exponent.sub_equiv

Topic: classical_mechanics   Node: f9e7552d5573

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.sub_equiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dimension.Exponent.sub_equiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Dimension.Exponent.sub_equiv (a b : Exponent) : equivRat (sub a b) = equivRat a - equivRat b := by
  rw [sub, add_equiv]
  simp [equivRat, sub_eq_add_neg]
