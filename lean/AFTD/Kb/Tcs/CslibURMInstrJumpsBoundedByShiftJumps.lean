import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrShiftJumps
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.JumpsBoundedBy.shiftJumps

Topic: computability   Node: 33bf6ee5e8d6

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.JumpsBoundedBy.shiftJumps`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

shiftJumps preserves bounded jumps with adjusted bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- shiftJumps preserves bounded jumps with adjusted bound. -/
theorem Cslib.URM.Instr.JumpsBoundedBy.shiftJumps {instr : Instr} {len offset : ℕ}
    (h : instr.JumpsBoundedBy len) :
    (instr.shiftJumps offset).JumpsBoundedBy (offset + len) := by
  cases instr with
  | J _ _ q => simp only [Instr.shiftJumps, JumpsBoundedBy] at h ⊢; omega
  | _ => trivial
