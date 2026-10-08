import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatSegmentIdem
import AFTD.Kb.Tcs.NatStrictMonoRangeGap
import AFTD.Kb.Tcs.NatNthOfStrictMono
import AFTD.Kb.Tcs.NatStrictMonoInfinite

/-!
# Nat.segment_range_val

Topic: algorithms   Node: 636ee825c254

Provenance: formalization of a published result. Source: CSLib, `Nat.segment_range_val`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ`, all `k` satisfying `f m ≤ k < f (m + 1)` has `segment f k = m`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ`, all `k` satisfying `f m ≤ k < f (m + 1)` has `segment f k = m`. -/
theorem Nat.segment_range_val (hm : StrictMono f) {m k : ℕ}
    (hl : f m ≤ k) (hu : k < f (m + 1)) : segment f k = m := by
  classical
  obtain (rfl | hu') := show f m = k ∨ f m < k by omega
  · exact segment_idem hm m
  · obtain ⟨j, h_j, rfl⟩ : ∃ j < f (m + 1) - f m - 1, k = j + f m + 1 := ⟨k - f m - 1, by omega⟩
    induction j
    case zero =>
      #adaptation_note
      /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
      have := strictMono_range_gap hm (show f m < f m + 1 by grind)
      have : count (· ∈ range f) (f m + 1 + 1) = count (· ∈ range f) (f m + 1) := by grind
      have := nth_of_strictMono hm m
      have := count_succ (· ∈ range f)
      simp_all only [segment, mem_range]
      split
      · grind [count_nth_of_infinite (strictMono_infinite hm) m]
      · grind
    case succ j _ =>
      have := strictMono_range_gap hm (show f m < j + 1 + f m     by grind)
      have := strictMono_range_gap hm (show f m < j + 1 + f m + 1 by grind)
      grind
