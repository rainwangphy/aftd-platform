import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump

/-!
# Cslib.URM.Instr.J_IsJump

Topic: computability   Node: dc5b6f618407

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.J_IsJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

J instruction is a jump.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- J instruction is a jump. -/
@[simp]
theorem Cslib.URM.Instr.J_IsJump (m n q : ℕ) : (J m n q).IsJump := trivial
