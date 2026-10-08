import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment_zero

Topic: algorithms   Node: 3965e8dc6af2

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_zero`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `segment f 0 = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `segment f 0 = 0`. -/
@[scoped grind =]
theorem Nat.segment_zero (hm : StrictMono f) (h0 : f 0 = 0) :
    segment f 0 = 0 := by
  calc _ = segment f (f 0) := by simp [h0]
       _ = _ := by simp [segment_idem hm]
