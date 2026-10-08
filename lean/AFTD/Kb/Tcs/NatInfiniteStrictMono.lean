import AFTD.Prelude

/-!
# Nat.infinite_strictMono

Topic: algorithms   Node: 1de05425d4d7

Provenance: formalization of a published result. Source: CSLib, `Nat.infinite_strictMono`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any infinite subset of `ℕ` is the range of a strictly monotonic function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- Any infinite subset of `ℕ` is the range of a strictly monotonic function. -/
theorem Nat.infinite_strictMono {ns : Set ℕ} (h : ns.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ range f = ns :=
  ⟨nth (· ∈ ns), nth_strictMono h, range_nth_of_infinite h⟩
