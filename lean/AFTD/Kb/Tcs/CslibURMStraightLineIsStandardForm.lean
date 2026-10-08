import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgramIsStandardForm
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedByOfNonJump
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormIdempotent
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgramInstDecidableIsStandardForm

/-!
# Cslib.URM.straight_line_IsStandardForm

Topic: computability   Node: a90e9191d65e

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.straight_line_IsStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Straight-line programs are in standard form.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Straight-line programs are in standard form. -/
theorem Cslib.URM.straight_line_IsStandardForm {p : Program} (hsl : p.IsStraightLine) :
    p.IsStandardForm := by
  intro instr hinstr
  exact Instr.jumpsBoundedBy_of_nonJump (hsl instr hinstr) p.length
