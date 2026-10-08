import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMStepOfNonJump
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMRegsWriteReadSelf
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMRegsWriteReadOfNe
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine
import AFTD.Kb.Tcs.CslibURMStateInstRepr
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMRegsWrite

/-!
# Cslib.URM.straight_line_halts_from_regs

Topic: computability   Node: 517301138a34

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.straight_line_halts_from_regs`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Straight-line programs halt from any starting registers, not just State.init. Useful for chaining: after running one program, we can run the next straight-line segment from whatever registers we're in.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Straight-line programs halt from any starting registers, not just State.init. Useful for chaining: after running one program, we can run the next straight-line segment from whatever registers we're in. -/
theorem Cslib.URM.straight_line_halts_from_regs {p : Program} (hsl : p.IsStraightLine) (r : Regs) :
    ∃ s, Steps p ⟨0, r⟩ s ∧ s.isHalted p ∧ s.pc = p.length := by
  suffices h : ∀ s : State, s.pc ≤ p.length → ∃ s', Steps p s s' ∧ s'.pc = p.length by
    obtain ⟨s', hsteps, hpc'⟩ := h ⟨0, r⟩ (Nat.zero_le _)
    exact ⟨s', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro s hpc_le
  generalize hrem : p.length - s.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing s with
  | h n ih =>
  by_cases hhalted : s.pc ≥ p.length
  · grind
  · have jmp : ¬p[s.pc].IsJump := by apply hsl; grind
    have := Step.of_nonJump (by lia) jmp
    grind [Relation.ReflTransGen.head]
