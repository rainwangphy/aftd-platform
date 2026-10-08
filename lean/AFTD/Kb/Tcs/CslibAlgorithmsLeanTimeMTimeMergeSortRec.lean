import AFTD.Prelude

/-!
# Cslib.Algorithms.Lean.TimeM.timeMergeSortRec

Topic: algorithms   Node: 13503c44d228

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.timeMergeSortRec`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Recurrence relation for the time complexity of merge sort. For a list of length `n`, this counts the total number of comparisons: - Base cases: 0 comparisons for lists of length 0 or 1 - Recursive case: split the list, sort both halves, then merge (which takes at most `n` comparisons)
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
/-- Recurrence relation for the time complexity of merge sort. For a list of length `n`, this counts the total number of comparisons: - Base cases: 0 comparisons for lists of length 0 or 1 - Recursive case: split the list, sort both halves, then merge (which takes at most `n` comparisons) -/
def Cslib.Algorithms.Lean.TimeM.timeMergeSortRec : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n
