import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMMerge
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetPure
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetMap
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeqRight
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeqLeft
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeq
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimePure
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeMap
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeqRight
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeqLeft
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeq
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetTick
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeTick
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqLeftOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqRightOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstMonadOfAddZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstLawfulMonad

/-!
# Cslib.Algorithms.Lean.TimeM.mergeSort

Topic: algorithms   Node: c6289ba01501

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.mergeSort`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sorts a list using the merge sort algorithm, counting comparisons as time cost. Returns a `TimeM ℕ (List α)` where the time represents the total number of comparisons.
-/

set_option relaxedAutoImplicit true in
open Cslib Cslib.Algorithms Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
/-- Sorts a list using the merge sort algorithm, counting comparisons as time cost. Returns a `TimeM ℕ (List α)` where the time represents the total number of comparisons. -/
def Cslib.Algorithms.Lean.TimeM.mergeSort (xs : List α) : TimeM ℕ (List α) :=  do
  if xs.length < 2 then return xs
  else
    let half  := xs.length / 2
    let left  := xs.take half
    let right := xs.drop half
    let sortedLeft  ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight
