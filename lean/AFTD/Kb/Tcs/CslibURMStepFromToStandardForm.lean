import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMProgramToStandardForm
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMInstrCapJump
import AFTD.Kb.Tcs.CslibURMProgramGetElemToStandardForm
import AFTD.Kb.Tcs.CslibURMRegsWriteReadSelf
import AFTD.Kb.Tcs.CslibURMRegsWriteReadOfNe
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMProgramToStandardFormLength
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
# Cslib.URM.Step.from_toStandardForm

Topic: computability   Node: 8940c8ea26c7

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step.from_toStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Reverse step correspondence: if p.toStandardForm steps from s to s', then either: (1) p steps from s to s' (same step), or (2) s' is halted in p.toStandardForm, and p steps to a state that is also halted with the same registers (this only happens for jumps with unbounded targets).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.URM.Program Cslib.URM.State Cslib.URM.Instr in
/-- Reverse step correspondence: if p.toStandardForm steps from s to s', then either: (1) p steps from s to s' (same step), or (2) s' is halted in p.toStandardForm, and p steps to a state that is also halted with the same registers (this only happens for jumps with unbounded targets). -/
theorem Cslib.URM.Step.from_toStandardForm {p : Program} {s s' : State} (hstep : Step p.toStandardForm s s') :
    Step p s s' ∨
    (s'.isHalted p.toStandardForm ∧ ∃ s₂, Step p s s₂ ∧ s₂.isHalted p ∧ s'.regs = s₂.regs) := by
  cases hstep with
  | jump_eq hinstr _ =>
    simp only [Program.getElem?_toStandardForm, Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, _⟩ := hinstr
    cases instr with
    | J => grind [=> jump_eq]
    | _ => grind
  | _ => grind [getElem?_toStandardForm, Option.map_eq_some_iff]
