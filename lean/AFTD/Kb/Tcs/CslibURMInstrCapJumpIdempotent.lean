import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.capJump_idempotent

Topic: computability   Node: b9da901bdff4

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.capJump_idempotent`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

capJump is idempotent: capping twice is the same as capping once.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- capJump is idempotent: capping twice is the same as capping once. -/
@[simp]
theorem Cslib.URM.Instr.capJump_idempotent (len : ℕ) (instr : Instr) :
    (instr.capJump len).capJump len = instr.capJump len := by
  cases instr with
  | Z | S | T => rfl
  | J m n q => simp [capJump]
