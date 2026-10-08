import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump

/-!
# Cslib.URM.Instr.Z_nonJump

Topic: computability   Node: 94c0595f8310

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.Z_nonJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Z instruction is not a jump.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Z instruction is not a jump. -/
@[simp]
theorem Cslib.URM.Instr.Z_nonJump (n : ℕ) : ¬(Z n).IsJump := not_false
