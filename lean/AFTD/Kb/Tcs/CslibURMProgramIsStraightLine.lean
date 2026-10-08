import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram

/-!
# Cslib.URM.Program.IsStraightLine

Topic: computability   Node: db4937cfd7d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.IsStraightLine`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A program is "straight-line" if it contains no jump instructions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A program is "straight-line" if it contains no jump instructions. -/
def Cslib.URM.Program.IsStraightLine (p : Program) : Prop :=
  ∀ i ∈ p, ¬i.IsJump
