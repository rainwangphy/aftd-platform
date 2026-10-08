import AFTD.Prelude
import AFTD.Kb.Tcs.NatStrictMonoInfinite
import AFTD.Kb.Tcs.NatNthSuccGap
import AFTD.Kb.Tcs.NatNthOfStrictMono

/-!
# Nat.strictMono_range_gap

Topic: algorithms   Node: 9276a1249ed7

Provenance: formalization of a published result. Source: CSLib, `Nat.strictMono_range_gap`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ`, no number (strictly) between `f m` and ` f (m + 1)` is in the range of `f`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ`, no number (strictly) between `f m` and ` f (m + 1)` is in the range of `f`. -/
theorem Nat.strictMono_range_gap (hm : StrictMono f) {m k : ℕ}
    (hl : f m < k) (hu : k < f (m + 1)) : k ∉ range f := by
  rw [nth_of_strictMono hm m] at hl
  rw [nth_of_strictMono hm (m + 1)] at hu
  have h_inf := strictMono_infinite hm
  have h_gap := nth_succ_gap (p := (· ∈ range f)) h_inf m
    (k - nth (· ∈ range f) m) (by omega) (by omega)
  rw [(show k - nth (· ∈ range f) m + nth (· ∈ range f) m = k by omega)] at h_gap
  exact h_gap
