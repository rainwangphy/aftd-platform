import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibOmegaSequenceIterate
import AFTD.Kb.Tcs.CslibOmegaSequenceTail
import AFTD.Kb.Tcs.CslibOmegaSequenceGetSucc
import AFTD.Kb.Tcs.CslibOmegaSequenceTailIterate
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
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceInstInhabited
import AFTD.Kb.Tcs.CslibOmegaSequenceInstIsEmpty

/-!
# Cslib.ωSequence.get_succ_iterate

Topic: algorithms   Node: 4f1419fa6fd1

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.get_succ_iterate`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Init.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.ωSequence.get_succ_iterate
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.ωSequence in
open Nat Function Option in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
variable (m n : ℕ) (x y : List α) (a b : ωSequence α) in
theorem Cslib.ωSequence.get_succ_iterate (n : ℕ) (f : α → α) (a : α) :
    iterate f a (succ n) = iterate f (f a) n := by
  rw [get_succ n (iterate f a), tail_iterate]
