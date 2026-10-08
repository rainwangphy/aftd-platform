import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMMergeSort
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeMergeSortRec
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMMerge
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMMergeTime
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMMergeSortSameLength
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetPure
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetMap
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeqRight
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeqLeft
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeq
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimePure
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeMap
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeqRight
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeqLeft
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeq
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetTick
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeTick
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetMerge
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqLeftOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqRightOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstMonadOfAddZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstLawfulMonad

/-!
# Cslib.Algorithms.Lean.TimeM.mergeSort_time_le

Topic: algorithms   Node: 1ee7c3feba2b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.mergeSort_time_le`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.mergeSort_time_le
-/

set_option relaxedAutoImplicit true in
open Cslib Cslib.Algorithms Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open Nat (clog) in
theorem Cslib.Algorithms.Lean.TimeM.mergeSort_time_le (xs : List α) :
    (mergeSort xs).time ≤ timeMergeSortRec xs.length := by
  fun_induction mergeSort with
  | case1 =>
    grind
  | case2 _ _ _ _ _ ih2 ih1 =>
    simp only [time_bind]
    grw [merge_time]
    simp only [mergeSort_same_length]
    unfold timeMergeSortRec
    grind
