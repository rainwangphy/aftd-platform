import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMProgramToStandardForm
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMProgramGetElemToStandardForm
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
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
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormIdempotent
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine
import AFTD.Kb.Tcs.CslibURMProgramInstDecidableIsStandardForm

/-!
# Cslib.URM.Step.toStandardForm

Topic: computability   Node: 69e75efa896d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step.toStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Forward step correspondence: if p steps from s to s', then either: (1) p.toStandardForm steps from s to s' (same step), or (2) s' is halted in p, and p.toStandardForm steps to a state that is also halted with the same registers (this only happens for jumps with unbounded targets).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Forward step correspondence: if p steps from s to s', then either: (1) p.toStandardForm steps from s to s' (same step), or (2) s' is halted in p, and p.toStandardForm steps to a state that is also halted with the same registers (this only happens for jumps with unbounded targets). -/
theorem Cslib.URM.Step.toStandardForm {p : Program} {s s' : State} (hstep : Step p s s') :
    Step p.toStandardForm s s' ∨
    (s'.isHalted p ∧ ∃ s₂, Step p.toStandardForm s s₂ ∧
      s₂.isHalted p.toStandardForm ∧ s'.regs = s₂.regs) := by
  cases hstep with
  | zero hinstr =>
    left
    exact Step.zero (by simp [Program.getElem?_toStandardForm, hinstr])
  | succ hinstr =>
    left
    exact Step.succ (by simp [Program.getElem?_toStandardForm, hinstr])
  | transfer hinstr =>
    left
    exact Step.transfer (by simp [Program.getElem?_toStandardForm, hinstr])
  | @jump_ne m n q hinstr hne =>
    left
    have hcap : p.toStandardForm[s.pc]? = some (Instr.J m n (min q p.length)) := by
      simp [Program.getElem?_toStandardForm, hinstr]
    exact Step.jump_ne hcap hne
  | @jump_eq m n q hinstr heq =>
    have (x : ℕ) (h : min q p.length = x) : p.toStandardForm[s.pc]? = some (Instr.J m n x) := by
      grind [Program.getElem?_toStandardForm, Instr.capJump]
    by_cases q ≤ p.length
    · grind [Step.jump_eq]
    · right
      split_ands
      · grind [State.isHalted]
      · use ⟨p.length, s.regs⟩
        grind [State.isHalted, Program.toStandardForm_length]
