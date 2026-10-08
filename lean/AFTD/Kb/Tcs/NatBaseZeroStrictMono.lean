import AFTD.Prelude

/-!
# Nat.base_zero_strictMono

Topic: algorithms   Node: 72645a730a57

Provenance: formalization of a published result. Source: CSLib, `Nat.base_zero_strictMono`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nat.base_zero_strictMono
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
theorem Nat.base_zero_strictMono (hm : StrictMono f) :
    StrictMono (f · - f 0) := by
  intro m n h_m_n; simp
  have := hm h_m_n
  have : f 0 ≤ f m := by simp [StrictMono.le_iff_le hm]
  have : f 0 ≤ f n := by simp [StrictMono.le_iff_le hm]
  omega
