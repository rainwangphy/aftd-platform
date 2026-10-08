import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump

/-!
# Cslib.URM.Instr.T_nonJump

Topic: computability   Node: d16a2d9c1ae5

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.T_nonJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

T instruction is not a jump.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- T instruction is not a jump. -/
@[simp]
theorem Cslib.URM.Instr.T_nonJump (m n : ℕ) : ¬(T m n).IsJump := not_false
