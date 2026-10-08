import AFTD.Prelude
import AFTD.Kb.Tcs.NatStrictMonoInfinite

/-!
# Nat.nth_of_strictMono

Topic: algorithms   Node: 91a4e5011627

Provenance: formalization of a published result. Source: CSLib, `Nat.nth_of_strictMono`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a strictly monotonic function `f : ℕ → ℕ`, `f n` is exactly the n-th element of the range of `f`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- For a strictly monotonic function `f : ℕ → ℕ`, `f n` is exactly the n-th element of the range of `f`. -/
theorem Nat.nth_of_strictMono (hm : StrictMono f) (n : ℕ) :
    f n = nth (· ∈ range f) n := by
  rw [← nth_comp_of_strictMono hm]
  · simp
  · simp
  · #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    intros
    have : (range f).Infinite := strictMono_infinite hm
    contradiction
