import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.jumpsBoundedBy_of_nonJump

Topic: computability   Node: 503a0d3401ee

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.jumpsBoundedBy_of_nonJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Non-jumping instructions have bounded jumps for any length.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Non-jumping instructions have bounded jumps for any length. -/
theorem Cslib.URM.Instr.jumpsBoundedBy_of_nonJump {instr : Instr} (h : ¬instr.IsJump)
    (len : ℕ) : instr.JumpsBoundedBy len := by
  cases instr with
  | J _ _ _ => exact absurd trivial h
  | _ => trivial
