import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.State.isHalted

Topic: computability   Node: 3e84935ba61f

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.isHalted`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is halted if the program counter is at or beyond the program length.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A state is halted if the program counter is at or beyond the program length. -/
@[scoped grind =]
def Cslib.URM.State.isHalted (s : State) (p : Program) : Prop := p.length ≤ s.pc
