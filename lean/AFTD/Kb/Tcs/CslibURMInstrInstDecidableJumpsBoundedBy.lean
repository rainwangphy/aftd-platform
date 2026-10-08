import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump

/-!
# Cslib.URM.Instr.instDecidableJumpsBoundedBy

Topic: computability   Node: a91926c5e621

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.instDecidableJumpsBoundedBy`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.Instr.instDecidableJumpsBoundedBy
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.Instr.instDecidableJumpsBoundedBy (len : ℕ) (instr : Instr) : Decidable (instr.JumpsBoundedBy len) := by
  cases instr <;> simp only [JumpsBoundedBy] <;> infer_instance
