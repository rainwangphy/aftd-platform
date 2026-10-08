import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatSegmentUpperBound
import AFTD.Kb.Tcs.NatSegmentLowerBound
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment_galois_connection

Topic: algorithms   Node: 52d9169fca23

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_galois_connection`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `f` and `segment f` form a Galois connection.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ` with `f 0 = 0`, `f` and `segment f` form a Galois connection. -/
theorem Nat.segment_galois_connection (hm : StrictMono f) (h0 : f 0 = 0) :
    GaloisConnection f (segment f) := by
  intro m k; constructor
  · intro h
    by_contra! h_con
    have h1 : segment f k + 1 ≤ m := by omega
    have := (StrictMono.le_iff_le hm).mpr h1
    have := segment_upper_bound hm h0 k
    omega
  · intro h
    by_contra! h_con
    have := (StrictMono.le_iff_le hm).mpr h
    have := segment_lower_bound hm h0 k
    omega
