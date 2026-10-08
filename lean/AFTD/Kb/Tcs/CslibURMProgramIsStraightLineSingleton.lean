import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine

/-!
# Cslib.URM.Program.IsStraightLine.singleton

Topic: computability   Node: 77c17ce71df0

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.IsStraightLine.singleton`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Singleton non-jumping instruction is straight-line.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Singleton non-jumping instruction is straight-line. -/
theorem Cslib.URM.Program.IsStraightLine.singleton {instr : Instr}
    (h : ¬instr.IsJump) : Program.IsStraightLine [instr] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  exact hi ▸ h
