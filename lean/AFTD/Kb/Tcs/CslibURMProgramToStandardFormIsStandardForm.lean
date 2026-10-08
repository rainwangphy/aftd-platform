import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStandardForm
import AFTD.Kb.Tcs.CslibURMProgramToStandardForm
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedByCapJump
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgramInstDecidableIsStandardForm

/-!
# Cslib.URM.Program.toStandardForm_isStandardForm

Topic: computability   Node: 9b984c201331

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.toStandardForm_isStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

toStandardForm produces a standard form program.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- toStandardForm produces a standard form program. -/
theorem Cslib.URM.Program.toStandardForm_isStandardForm (p : Program) :
    p.toStandardForm.IsStandardForm := by
  unfold IsStandardForm toStandardForm
  rw [List.length_map]
  intro instr hinstr
  obtain ⟨orig, _, rfl⟩ := List.mem_map.mp hinstr
  exact Instr.JumpsBoundedBy.capJump p.length orig
