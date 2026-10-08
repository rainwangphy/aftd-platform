import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.JumpsBoundedBy.mono

Topic: computability   Node: 18946803b4d8

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.JumpsBoundedBy.mono`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JumpsBoundedBy is monotonic: if bounded for len1, then bounded for any len2 ≥ len1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- JumpsBoundedBy is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem Cslib.URM.Instr.JumpsBoundedBy.mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.JumpsBoundedBy len1) (hle : len1 ≤ len2) :
    instr.JumpsBoundedBy len2 := by
  grind [JumpsBoundedBy]
