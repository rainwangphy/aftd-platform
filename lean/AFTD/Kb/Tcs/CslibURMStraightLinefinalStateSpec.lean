import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStraightLinefinalState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMStraightLineHaltsFromRegs
import AFTD.Kb.Tcs.CslibURMRegsWriteReadSelf
import AFTD.Kb.Tcs.CslibURMRegsWriteReadOfNe
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMInstrZNonJump
import AFTD.Kb.Tcs.CslibURMInstrSNonJump
import AFTD.Kb.Tcs.CslibURMInstrTNonJump
import AFTD.Kb.Tcs.CslibURMInstrJIsJump
import AFTD.Kb.Tcs.CslibURMInstrCapJumpZ
import AFTD.Kb.Tcs.CslibURMInstrCapJumpS
import AFTD.Kb.Tcs.CslibURMInstrCapJumpT
import AFTD.Kb.Tcs.CslibURMInstrCapJumpJ
import AFTD.Kb.Tcs.CslibURMInstrCapJumpIdempotent
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine

/-!
# Cslib.URM.straightLinefinalState_spec

Topic: computability   Node: bdfd3aa80cc9

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.straightLinefinalState_spec`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Specification: the state from straightLinefinalState satisfies Steps, isHalted, and has pc = p.length.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Specification: the state from straightLinefinalState satisfies Steps, isHalted, and has pc = p.length. -/
theorem Cslib.URM.straightLinefinalState_spec {p : Program} (hsl : p.IsStraightLine) (r : Regs) :
    let s := straightLinefinalState hsl r
    Steps p ⟨0, r⟩ s ∧ s.isHalted p ∧ s.pc = p.length :=
  Classical.choose_spec (straight_line_halts_from_regs hsl r)
