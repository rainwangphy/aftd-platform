import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump

/-!
# Cslib.URM.Instr.JumpsBoundedBy

Topic: computability   Node: 0ab6223cb95b

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.JumpsBoundedBy`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instruction's jump target is bounded by a given length. Non-jump instructions trivially satisfy this.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instruction's jump target is bounded by a given length. Non-jump instructions trivially satisfy this. -/
def Cslib.URM.Instr.JumpsBoundedBy (len : ℕ) : Instr → Prop
  | J _ _ q => q ≤ len
  | _ => True
