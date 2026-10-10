import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexToList
import AFTD.Kb.Physics.PhyslibMultiIndexOrder
import AFTD.Kb.Physics.PhyslibMultiIndexTail
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplyNe
import AFTD.Kb.Physics.PhyslibMultiIndexOrderZero
import AFTD.Kb.Physics.PhyslibMultiIndexOrderSingle
import AFTD.Kb.Physics.PhyslibMultiIndexOrderIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexTailZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementSucc
import AFTD.Kb.Physics.PhyslibMultiIndexToListZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAlice

/-!
# Physlib.MultiIndex.length_toList

Topic: classical_mechanics   Node: fe0655e3eed9

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.length_toList`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.length_toList
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
lemma Physlib.MultiIndex.length_toList (I : MultiIndex d) : I.toList.length = I.order := by
  induction d with
  | zero =>
      simp [toList, MultiIndex.order]
  | succ d ih =>
      simp [toList, tail, MultiIndex.order, Fin.sum_univ_succ, ih]
