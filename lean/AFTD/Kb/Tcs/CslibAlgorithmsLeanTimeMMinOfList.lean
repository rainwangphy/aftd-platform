import AFTD.Prelude

/-!
# Cslib.Algorithms.Lean.TimeM.MinOfList

Topic: algorithms   Node: 82a9e0b7450f

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.MinOfList`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`x` is a minimum element of list `l` if `x ≤ b` for all `b ∈ l`.
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open List in
/-- `x` is a minimum element of list `l` if `x ≤ b` for all `b ∈ l`. -/
abbrev Cslib.Algorithms.Lean.TimeM.MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b
