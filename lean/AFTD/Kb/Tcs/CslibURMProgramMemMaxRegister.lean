import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrMaxRegister
import AFTD.Kb.Tcs.CslibURMProgramMaxRegister
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy

/-!
# Cslib.URM.Program.mem_maxRegister

Topic: computability   Node: 64d7c3b8c9ab

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.mem_maxRegister`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any instruction in a program has maxRegister at most the program's maxRegister.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Any instruction in a program has maxRegister at most the program's maxRegister. -/
theorem Cslib.URM.Program.mem_maxRegister {p : Program} {instr : Instr} (h : instr ∈ p) :
    instr.maxRegister ≤ p.maxRegister := by
  unfold maxRegister
  rw [List.foldl_map.symm, ←List.foldr_eq_foldl]
  exact List.le_max_of_le' 0 (List.mem_map.mpr ⟨instr, h, rfl⟩) (le_refl _)
