import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment_pre_zero

Topic: algorithms   Node: c6becdf66315

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_pre_zero`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ`, `segment f k = 0` for all `k < f 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ`, `segment f k = 0` for all `k < f 0`. -/
@[scoped grind =]
theorem Nat.segment_pre_zero (hm : StrictMono f) {k : ℕ} (h : k < f 0) :
    segment f k = 0 := by
  classical
  have h1 : count (· ∈ range f) (k + 1) = 0 := by
    apply count_of_forall_not
    rintro n h_n ⟨i, rfl⟩
    have := StrictMono.monotone hm <| zero_le i
    omega
  rw [segment, h1]
