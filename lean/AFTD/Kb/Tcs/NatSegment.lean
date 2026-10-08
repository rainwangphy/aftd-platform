import AFTD.Prelude

/-!
# Nat.segment

Topic: algorithms   Node: 6641d9430fcd

Provenance: formalization of a published result. Source: CSLib, `Nat.segment`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `f`-segment of `k`, where `f : ℕ → ℕ` will be assumed to be at least StrictMono.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
/-- The `f`-segment of `k`, where `f : ℕ → ℕ` will be assumed to be at least StrictMono. -/
@[scoped grind]
noncomputable def Nat.segment (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  open scoped Classical in
  Nat.count (· ∈ range f) (k + 1) - 1
