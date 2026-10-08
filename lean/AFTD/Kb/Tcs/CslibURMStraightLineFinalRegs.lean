import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStraightLinefinalState
import AFTD.Kb.Tcs.CslibURMRegsWriteReadSelf
import AFTD.Kb.Tcs.CslibURMRegsWriteReadOfNe
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine

/-!
# Cslib.URM.straightLineFinalRegs

Topic: computability   Node: 4f2add7dc5ef

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.straightLineFinalRegs`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The final registers after running a straight-line program from given starting registers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The final registers after running a straight-line program from given starting registers. -/
noncomputable def Cslib.URM.straightLineFinalRegs {p : Program} (hsl : p.IsStraightLine) (r : Regs) : Regs :=
  (straightLinefinalState hsl r).regs
