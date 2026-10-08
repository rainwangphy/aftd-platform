import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.JumpsBoundedBy.capJump

Topic: computability   Node: c0295943c22f

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.JumpsBoundedBy.capJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

capJump always produces an instruction with bounded jump.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- capJump always produces an instruction with bounded jump. -/
theorem Cslib.URM.Instr.JumpsBoundedBy.capJump (len : ℕ) (instr : Instr) :
    (instr.capJump len).JumpsBoundedBy len := by
  cases instr with
  | J _ _ q => exact Nat.min_le_right q len
  | _ => trivial
