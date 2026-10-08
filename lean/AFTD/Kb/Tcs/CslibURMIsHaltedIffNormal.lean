import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.RelationNormal
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.RelationReducible
import AFTD.Kb.Tcs.CslibURMStepNoStepOfHalted
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.isHalted_iff_normal

Topic: computability   Node: 7fc93959a45d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.isHalted_iff_normal`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is halted iff it is normal (has no successor) in the reduction system.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- A state is halted iff it is normal (has no successor) in the reduction system. -/
theorem Cslib.URM.isHalted_iff_normal {p : Program} {s : State} :
    s.isHalted p ↔ Relation.Normal (Step p) s := by
  constructor
  · intro hhalted ⟨s', hstep⟩
    exact Step.no_step_of_halted hhalted hstep
  · intro hnormal
    -- If not halted, then p[s.pc]? = some instr for some instruction
    by_contra hnothalted
    simp only [State.isHalted, not_le] at hnothalted
    have hlt : s.pc < p.length := hnothalted
    have hinstr : p[s.pc]? = some p[s.pc] := List.getElem?_eq_getElem hlt
    -- Any instruction can step, contradicting hnormal
    cases hp : p[s.pc] with
    | Z n => exact hnormal ⟨_, Step.zero (hp ▸ hinstr)⟩
    | S n => exact hnormal ⟨_, Step.succ (hp ▸ hinstr)⟩
    | T m n => exact hnormal ⟨_, Step.transfer (hp ▸ hinstr)⟩
    | J m n q =>
      by_cases heq : s.regs.read m = s.regs.read n
      · exact hnormal ⟨_, Step.jump_eq (hp ▸ hinstr) heq⟩
      · exact hnormal ⟨_, Step.jump_ne (hp ▸ hinstr) heq⟩
