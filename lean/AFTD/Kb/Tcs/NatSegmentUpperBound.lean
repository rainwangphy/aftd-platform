import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatNthOfStrictMono
import AFTD.Kb.Tcs.NatSegmentPlusOne
import AFTD.Kb.Tcs.NatStrictMonoInfinite
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment_upper_bound

Topic: algorithms   Node: 2e5d75d5314b

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_upper_bound`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `k < f (segment f k + 1)` for all `k : ℕ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `k < f (segment f k + 1)` for all `k : ℕ`. -/
theorem Nat.segment_upper_bound (hm : StrictMono f) (h0 : f 0 = 0) (k : ℕ) :
    k < f (segment f k + 1) := by
  classical
  rw [nth_of_strictMono hm (segment f k + 1), segment_plus_one h0 k]
  suffices _ : k + 1 ≤ nth (· ∈ range f) (count (· ∈ range f) (k + 1)) by omega
  apply le_nth_count
  exact strictMono_infinite hm
