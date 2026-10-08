import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMRegsRead
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
# Cslib.URM.Step.of_nonJump

Topic: computability   Node: 61df4736dbb4

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step.of_nonJump`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A non-jumping instruction produces a step that increments PC by 1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A non-jumping instruction produces a step that increments PC by 1. -/
theorem Cslib.URM.Step.of_nonJump {p : Program} {s : State} (hlt : s.pc < p.length)
    (hnonjump : ¬(p[s.pc]'hlt).IsJump) :
    ∃ s', Step p s s' ∧ s'.pc = s.pc + 1 := by
  cases hp : (p[s.pc]'hlt) with
  | Z n =>
    use {pc := s.pc + 1, regs := s.regs.write n 0}
    grind
  | S n =>
    use { pc := s.pc + 1, regs := s.regs.write n (s.regs.read n + 1) }
    grind
  | T m n =>
    use { pc := s.pc + 1, regs := s.regs.write n (s.regs.read m) }
    grind
  | J _ _ _ => grind [Instr.IsJump]
