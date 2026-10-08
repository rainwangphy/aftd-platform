import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrShiftJumps

/-!
# Cslib.URM.Program.shiftJumps

Topic: computability   Node: 453d72dbdea9

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.shiftJumps`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shift all jump targets in a program by `offset`. Used when concatenating programs: the second program's jumps must be adjusted by the length of the first program.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Shift all jump targets in a program by `offset`. Used when concatenating programs: the second program's jumps must be adjusted by the length of the first program. -/
@[scoped grind =]
def Cslib.URM.Program.shiftJumps (p : Program) (offset : ℕ) : Program :=
  p.map (Instr.shiftJumps offset)
