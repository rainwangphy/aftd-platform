import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStraightLine
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrIsJump
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram

/-!
# Cslib.URM.instDecidableIsStraightLine

Topic: computability   Node: b066faafc4e2

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.instDecidableIsStraightLine`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StraightLine.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.instDecidableIsStraightLine
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.instDecidableIsStraightLine (p : Program) : Decidable p.IsStraightLine :=
  inferInstanceAs (Decidable (∀ i ∈ p, ¬i.IsJump))
