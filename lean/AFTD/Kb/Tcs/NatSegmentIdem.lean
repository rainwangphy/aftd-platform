import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatStrictMonoInfinite
import AFTD.Kb.Tcs.NatNthOfStrictMono

/-!
# Nat.segment_idem

Topic: algorithms   Node: d06f44161063

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_idem`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ`, the segment of `f k` is `k`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ`, the segment of `f k` is `k`. -/
@[simp]
theorem Nat.segment_idem (hm : StrictMono f) (k : ℕ) :
    segment f (f k) = k := by
  classical
  have := count_nth_of_infinite (p := (· ∈ range f)) <| strictMono_infinite hm
  have := nth_of_strictMono hm
  grind [segment]
