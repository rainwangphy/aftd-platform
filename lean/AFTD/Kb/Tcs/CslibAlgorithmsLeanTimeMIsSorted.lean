import AFTD.Prelude

/-!
# Cslib.Algorithms.Lean.TimeM.IsSorted

Topic: algorithms   Node: 4838e95502ca

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.IsSorted`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate.
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open List in
/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev Cslib.Algorithms.Lean.TimeM.IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l
