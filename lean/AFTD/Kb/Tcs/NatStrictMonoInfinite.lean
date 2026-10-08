import AFTD.Prelude

/-!
# Nat.strictMono_infinite

Topic: algorithms   Node: 537b3727e3fb

Provenance: formalization of a published result. Source: CSLib, `Nat.strictMono_infinite`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any strictly monotonic function `f : ℕ → ℕ` has an infinite range.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- Any strictly monotonic function `f : ℕ → ℕ` has an infinite range. -/
theorem Nat.strictMono_infinite (hm : StrictMono f) :
    (range f).Infinite :=
  infinite_range_of_injective hm.injective
