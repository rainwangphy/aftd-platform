import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrWritesTo
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Step.preserves_register

Topic: computability   Node: 9197f9796c3c

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step.preserves_register`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A single step preserves registers not written to by the current instruction. This is a fundamental property of URM execution: each instruction modifies at most one register (Z, S, T write to one register; J writes to none).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
variable {p : Program} in
/-- A single step preserves registers not written to by the current instruction. This is a fundamental property of URM execution: each instruction modifies at most one register (Z, S, T write to one register; J writes to none). -/
theorem Cslib.URM.Step.preserves_register {s s' : State} {r : ℕ}
    (hstep : Step p s s')
    (hr : ∀ instr, p[s.pc]? = some instr → instr.writesTo ≠ some r) :
    s'.regs.read r = s.regs.read r := by
  cases hstep with
  | zero hinstr | succ hinstr | transfer hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq _ _ | jump_ne _ _ => rfl
