import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMClog2HalfLe

/-!
# Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le

Topic: algorithms   Node: 9d898abb5e7f

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open Nat (clog) in
/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind →]
lemma Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le (n : ℕ) (h : n > 1) : clog 2 (n / 2) ≤ clog 2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n h)
  apply Nat.clog_monotone
  grind
