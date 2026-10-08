import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstrShiftJumps
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump

/-!
# Cslib.URM.Instr.shiftJumps_of_nonJump

Topic: computability   Node: 80d1714b4d66

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.shiftJumps_of_nonJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

shiftJumps is identity for non-jumping instructions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- shiftJumps is identity for non-jumping instructions. -/
theorem Cslib.URM.Instr.shiftJumps_of_nonJump {instr : Instr}
    (h : ¬instr.IsJump) (offset : ℕ) : instr.shiftJumps offset = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ _ => exact absurd trivial h
