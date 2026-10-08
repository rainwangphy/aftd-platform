import AFTD.Prelude

/-!
# Nat.base_zero_shift

Topic: algorithms   Node: 05accd6aa7f7

Provenance: formalization of a published result. Source: CSLib, `Nat.base_zero_shift`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nat.base_zero_shift
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
lemma Nat.base_zero_shift (f : ℕ → ℕ) :
    (f · - f 0) 0 = 0 := by
  simp
