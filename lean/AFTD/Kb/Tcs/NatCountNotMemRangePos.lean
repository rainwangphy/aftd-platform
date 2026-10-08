import AFTD.Prelude

/-!
# Nat.count_notMem_range_pos

Topic: algorithms   Node: a408a43e6860

Provenance: formalization of a published result. Source: CSLib, `Nat.count_notMem_range_pos`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `f 0 = 0`, then `0` is below any `n` not in the range of `f`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
open scoped Classical in
/-- If `f 0 = 0`, then `0` is below any `n` not in the range of `f`. -/
theorem Nat.count_notMem_range_pos (h0 : f 0 = 0) (n : ℕ) (hn : n ∉ range f) :
    count (· ∈ range f) n > 0 := by
  have := count_monotone (· ∈ range f) (show 1 ≤ n by grind)
  grind
