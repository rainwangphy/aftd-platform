import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment_plus_one

Topic: algorithms   Node: cc418c787f56

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_plus_one`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A slight restatement of the definition of `segment` which has proven useful.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
open scoped Classical in
/-- A slight restatement of the definition of `segment` which has proven useful. -/
theorem Nat.segment_plus_one (h0 : f 0 = 0) (k : ℕ) :
    segment f k + 1 = count (· ∈ range f) (k + 1) := by
  suffices _ : count (· ∈ range f) (k + 1) ≠ 0 by unfold segment; omega
  apply count_ne_iff_exists.mpr; use 0; grind
