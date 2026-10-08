import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceTake
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibOmegaSequenceGetElemTake
import AFTD.Kb.Tcs.CslibOmegaSequenceEta
import AFTD.Kb.Tcs.CslibOmegaSequenceGetFun
import AFTD.Kb.Tcs.CslibOmegaSequenceGetZeroCons
import AFTD.Kb.Tcs.CslibOmegaSequenceHeadCons
import AFTD.Kb.Tcs.CslibOmegaSequenceTailCons
import AFTD.Kb.Tcs.CslibOmegaSequenceGetDrop
import AFTD.Kb.Tcs.CslibOmegaSequenceDropDrop
import AFTD.Kb.Tcs.CslibOmegaSequenceGetTail
import AFTD.Kb.Tcs.CslibOmegaSequenceTailDrop'
import AFTD.Kb.Tcs.CslibOmegaSequenceDropTail'
import AFTD.Kb.Tcs.CslibOmegaSequenceGetSuccCons
import AFTD.Kb.Tcs.CslibOmegaSequenceGetConsAppendZero
import AFTD.Kb.Tcs.CslibOmegaSequenceAppendEqCons
import AFTD.Kb.Tcs.CslibOmegaSequenceDropZero
import AFTD.Kb.Tcs.CslibOmegaSequenceGetMap
import AFTD.Kb.Tcs.CslibOmegaSequenceHeadMap
import AFTD.Kb.Tcs.CslibOmegaSequenceMapId
import AFTD.Kb.Tcs.CslibOmegaSequenceMapMap
import AFTD.Kb.Tcs.CslibOmegaSequenceMapTail
import AFTD.Kb.Tcs.CslibOmegaSequenceGetZip
import AFTD.Kb.Tcs.CslibOmegaSequenceTailConst
import AFTD.Kb.Tcs.CslibOmegaSequenceMapConst
import AFTD.Kb.Tcs.CslibOmegaSequenceGetConst
import AFTD.Kb.Tcs.CslibOmegaSequenceDropConst
import AFTD.Kb.Tcs.CslibOmegaSequenceHeadIterate
import AFTD.Kb.Tcs.CslibOmegaSequenceGetZeroIterate
import AFTD.Kb.Tcs.CslibOmegaSequenceIterateId
import AFTD.Kb.Tcs.CslibOmegaSequenceNilAppendOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceAppendAppendOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceGetAppendRight
import AFTD.Kb.Tcs.CslibOmegaSequenceGetAppendLength
import AFTD.Kb.Tcs.CslibOmegaSequenceAppendRightInj
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeZero
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeSuccCons
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeOne
import AFTD.Kb.Tcs.CslibOmegaSequenceLengthTake
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeTake
import AFTD.Kb.Tcs.CslibOmegaSequenceConcatTakeGet
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceInstInhabited
import AFTD.Kb.Tcs.CslibOmegaSequenceInstIsEmpty

/-!
# Cslib.ωSequence.getElem?_take_succ

Topic: algorithms   Node: 9f88095ac9a1

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.getElem?_take_succ`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Init.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.ωSequence.getElem?_take_succ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.ωSequence in
open Nat Function Option in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
variable (m n : ℕ) (x y : List α) (a b : ωSequence α) in
theorem Cslib.ωSequence.getElem?_take_succ (n : ℕ) (s : ωSequence α) :
    (take (succ n) s)[n]? = some (s n) :=
  getElem?_take (Nat.lt_succ_self n)
