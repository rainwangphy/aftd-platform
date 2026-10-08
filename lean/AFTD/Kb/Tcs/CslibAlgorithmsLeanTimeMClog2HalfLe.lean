import AFTD.Prelude

/-!
# Cslib.Algorithms.Lean.TimeM.clog2_half_le

Topic: algorithms   Node: 0b1898efa5ab

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.clog2_half_le`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open Nat (clog) in
/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1 -/
@[grind →]
lemma Cslib.Algorithms.Lean.TimeM.clog2_half_le (n : ℕ) (h : n > 1) : clog 2 ((n + 1) / 2) ≤ clog 2 n - 1 := by
  grind [Nat.clog_of_one_lt one_lt_two h]
