import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine

/-!
# Cslib.URM.Program.IsStraightLine.cons

Topic: computability   Node: 658c6b660a9a

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.IsStraightLine.cons`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cons of non-jumping instruction preserves straight-line.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Cons of non-jumping instruction preserves straight-line. -/
theorem Cslib.URM.Program.IsStraightLine.cons {instr : Instr} {p : Program}
    (hinstr : ¬instr.IsJump) (hp : p.IsStraightLine) :
    Program.IsStraightLine (instr :: p) := by
  intro i hi
  simp only [List.mem_cons] at hi
  rcases hi with rfl | hi <;> [exact hinstr; exact hp i hi]
