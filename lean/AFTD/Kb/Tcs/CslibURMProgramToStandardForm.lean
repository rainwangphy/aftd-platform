import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgramInstDecidableIsStandardForm

/-!
# Cslib.URM.Program.toStandardForm

Topic: computability   Node: aef928a12ef3

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.toStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convert a program to standard form by capping all jump targets at the program length.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Convert a program to standard form by capping all jump targets at the program length. -/
def Cslib.URM.Program.toStandardForm (p : Program) : Program :=
  p.map (Instr.capJump p.length)
