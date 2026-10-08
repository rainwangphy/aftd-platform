import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump

/-!
# Cslib.URM.Instr.instDecidableIsJump

Topic: computability   Node: 75b0b9c7b7ef

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.instDecidableIsJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.Instr.instDecidableIsJump
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.Instr.instDecidableIsJump (instr : Instr) : Decidable instr.IsJump := by
  cases instr <;> simp only [IsJump] <;> infer_instance
