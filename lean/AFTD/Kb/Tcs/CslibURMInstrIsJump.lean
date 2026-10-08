import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.Instr.IsJump

Topic: computability   Node: 0d5f7479e163

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.IsJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instruction is a jump instruction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instruction is a jump instruction. -/
def Cslib.URM.Instr.IsJump : Instr → Prop
  | J _ _ _ => True
  | _ => False
