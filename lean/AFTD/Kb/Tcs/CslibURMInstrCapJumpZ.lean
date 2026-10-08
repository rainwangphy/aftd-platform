import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Instr.capJump_Z

Topic: computability   Node: ce557afad028

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.capJump_Z`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.Instr.capJump_Z
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
theorem Cslib.URM.Instr.capJump_Z (len n : ℕ) : (Z n).capJump len = Z n := rfl
