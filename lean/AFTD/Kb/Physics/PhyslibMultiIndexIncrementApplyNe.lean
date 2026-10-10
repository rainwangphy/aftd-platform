import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.increment_apply_ne

Topic: classical_mechanics   Node: 803d915d2656

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.increment_apply_ne`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.increment_apply_ne
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
@[simp]
lemma Physlib.MultiIndex.increment_apply_ne (I : MultiIndex d) {i j : Fin d} (h : j ≠ i) :
    increment I i j = I j := by
  simp [increment, Pi.single_eq_of_ne h]
