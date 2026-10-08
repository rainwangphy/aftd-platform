import AFTD.Prelude
import AFTD.Kb.Tcs.NatSegment
import AFTD.Kb.Tcs.NatSegmentIdem

/-!
# Nat.segment'

Topic: algorithms   Node: 084f8ff89626

Provenance: formalization of a published result. Source: CSLib, `Nat.segment'`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`segment'` is a helper function that will be proved to be equal to `segment`. It facilitates the proofs of some theorems below.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- `segment'` is a helper function that will be proved to be equal to `segment`. It facilitates the proofs of some theorems below. -/
noncomputable def Nat.segment' (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  segment (f · - f 0) (k - f 0)
