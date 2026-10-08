import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatNthOfStrictMono
import AFTD.Kb.Tcs.NatCountNotMemRangePos
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment_lower_bound

Topic: algorithms   Node: 4c558cf88378

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_lower_bound`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `f (segment f k) ≤ k` for all `k : ℕ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `f (segment f k) ≤ k` for all `k : ℕ`. -/
theorem Nat.segment_lower_bound (hm : StrictMono f) (h0 : f 0 = 0) (k : ℕ) :
    f (segment f k) ≤ k := by
  classical
  rw [nth_of_strictMono hm (segment f k), segment]
  rcases Classical.em (k ∈ range f) with h_k | h_k
  · simp_all [count_succ_eq_succ_count]
  · have h1 : count (· ∈ range f) k > 0 := count_notMem_range_pos h0 k h_k
    have h2 : count (· ∈ range f) (k + 1) = count (· ∈ range f) k :=
      count_succ_eq_count h_k
    rw [h2]
    suffices _ : nth (· ∈ range f) (count (· ∈ range f) k - 1) < k by omega
    apply nth_lt_of_lt_count
    omega
