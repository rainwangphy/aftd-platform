import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexToList
import AFTD.Kb.Physics.PhyslibMultiIndexIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexTail
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplyNe
import AFTD.Kb.Physics.PhyslibMultiIndexOrderZero
import AFTD.Kb.Physics.PhyslibMultiIndexOrderSingle
import AFTD.Kb.Physics.PhyslibMultiIndexOrderIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexTailZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementSucc
import AFTD.Kb.Physics.PhyslibMultiIndexToListZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAlice

/-!
# Physlib.MultiIndex.toList_increment_zero

Topic: classical_mechanics   Node: ddc5d4630685

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.toList_increment_zero`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.toList_increment_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
@[simp]
lemma Physlib.MultiIndex.toList_increment_zero (I : MultiIndex d.succ) :
    toList (increment I 0) = 0 :: toList I := by
  simp only [toList, increment_apply_same, tail_increment_zero]
  rw [show I 0 + 1 = 1 + I 0 by omega, List.replicate_add]
  simp
