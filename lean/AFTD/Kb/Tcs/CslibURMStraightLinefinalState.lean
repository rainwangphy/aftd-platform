import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMStraightLineHaltsFromRegs
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
# Cslib.URM.straightLinefinalState

Topic: computability   Node: ea6f2d9f95a3

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.straightLinefinalState`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The halting state for a straight-line program starting from registers r. Wraps Classical.choose to hide it from the API.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The halting state for a straight-line program starting from registers r. Wraps Classical.choose to hide it from the API. -/
noncomputable def Cslib.URM.straightLinefinalState {p : Program}
    (hsl : p.IsStraightLine) (r : Regs) : State :=
  Classical.choose (straight_line_halts_from_regs hsl r)
