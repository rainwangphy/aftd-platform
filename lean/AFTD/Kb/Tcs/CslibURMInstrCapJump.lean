import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.capJump

Topic: computability   Node: 21ae6634558d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.capJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cap a jump target to be at most `len`. Non-jump instructions are unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Cap a jump target to be at most `len`. Non-jump instructions are unchanged. -/
@[scoped grind =]
def Cslib.URM.Instr.capJump (len : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (min q len)
