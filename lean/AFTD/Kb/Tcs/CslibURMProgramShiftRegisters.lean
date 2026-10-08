import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrShiftRegisters

/-!
# Cslib.URM.Program.shiftRegisters

Topic: computability   Node: 007a9b5a06da

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.shiftRegisters`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shift all register references in a program by `offset`. Used to isolate register usage when composing programs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Shift all register references in a program by `offset`. Used to isolate register usage when composing programs. -/
@[scoped grind =]
def Cslib.URM.Program.shiftRegisters (p : Program) (offset : ℕ) : Program :=
  p.map (Instr.shiftRegisters offset)
