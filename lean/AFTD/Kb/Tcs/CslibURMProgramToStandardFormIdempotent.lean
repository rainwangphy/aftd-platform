import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramToStandardForm
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMInstrCapJumpIdempotent
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgramInstDecidableIsStandardForm

/-!
# Cslib.URM.Program.toStandardForm_idempotent

Topic: computability   Node: b28620ebca0b

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.toStandardForm_idempotent`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

toStandardForm is idempotent: applying it twice equals applying it once.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- toStandardForm is idempotent: applying it twice equals applying it once. -/
@[simp]
theorem Cslib.URM.Program.toStandardForm_idempotent (p : Program) :
    p.toStandardForm.toStandardForm = p.toStandardForm := by
  simp only [toStandardForm, List.length_map, List.map_map]
  congr 1
  funext instr
  exact Instr.capJump_idempotent p.length instr
