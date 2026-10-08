import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine

/-!
# Cslib.URM.Program.IsStandardForm

Topic: computability   Node: 64a2a4d333aa

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.IsStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A program is in standard form if all jump targets are bounded by the program length. Jumps can target any instruction (0..length-1) or the "virtual halt" position (length).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A program is in standard form if all jump targets are bounded by the program length. Jumps can target any instruction (0..length-1) or the "virtual halt" position (length). -/
def Cslib.URM.Program.IsStandardForm (p : Program) : Prop :=
  ∀ instr ∈ p, instr.JumpsBoundedBy p.length
