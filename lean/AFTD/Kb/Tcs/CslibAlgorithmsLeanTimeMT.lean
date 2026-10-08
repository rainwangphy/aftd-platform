import AFTD.Prelude

/-!
# Cslib.Algorithms.Lean.TimeM.T

Topic: algorithms   Node: 1b9286cb4d0c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.T`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Upper bound function for merge sort time complexity: `T(n) = n * ⌈log₂ n⌉`
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open Nat (clog) in
/-- Upper bound function for merge sort time complexity: `T(n) = n * ⌈log₂ n⌉` -/
abbrev Cslib.Algorithms.Lean.TimeM.T (n : ℕ) : ℕ := n * clog 2 n
