import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndexToList
import AFTD.Kb.Physics.PhyslibMultiIndexIncrement
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexToListIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexToListZero
import AFTD.Kb.Physics.PhyslibMultiIndexTail
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementSucc
import AFTD.Kb.Physics.PhyslibMultiIndexTailZero
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplyNe
import AFTD.Kb.Physics.PhyslibMultiIndexOrderZero
import AFTD.Kb.Physics.PhyslibMultiIndexOrderSingle
import AFTD.Kb.Physics.PhyslibMultiIndexOrderIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAlice

/-!
# Physlib.MultiIndex.toList_single

Topic: classical_mechanics   Node: 0fb9648110c5

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.toList_single`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.toList_single
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
@[simp]
lemma Physlib.MultiIndex.toList_single (i : Fin d) : toList (increment 0 i : MultiIndex d) = [i] := by
  induction d with
  | zero =>
      exact Fin.elim0 i
  | succ d ih =>
      refine Fin.cases ?_ ?_ i
      · simp [toList_increment_zero]
      · intro j
        have htail :
            tail (increment (0 : MultiIndex d.succ) j.succ) = increment (0 : MultiIndex d) j := by
          rw [tail_increment_succ, tail_zero]
        have hzero : increment (0 : MultiIndex d.succ) j.succ 0 = 0 := by
          simp [increment]
        simp [toList, hzero, htail, ih j]
