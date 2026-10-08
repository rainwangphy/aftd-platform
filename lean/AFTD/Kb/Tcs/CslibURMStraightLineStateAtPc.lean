import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMStepOfNonJump
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
# Cslib.URM.straight_line_state_at_pc

Topic: computability   Node: ae9a0fc4a24f

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.straight_line_state_at_pc`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a straight-line program, we can characterize the state at any intermediate pc. This gives us the state after executing instructions 0..pc-1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- In a straight-line program, we can characterize the state at any intermediate pc. This gives us the state after executing instructions 0..pc-1. -/
theorem Cslib.URM.straight_line_state_at_pc {p : Program} (hsl : p.IsStraightLine)
    (r : Regs) (targetPc : ℕ) (htarget : targetPc ≤ p.length) :
    ∃ s, Steps p ⟨0, r⟩ s ∧ s.pc = targetPc := by
  induction targetPc with
  | zero => exact ⟨⟨0, r⟩, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih => grind [Step.of_nonJump, Program.IsStraightLine]
