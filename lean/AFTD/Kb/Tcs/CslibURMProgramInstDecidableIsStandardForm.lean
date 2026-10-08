import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramIsStandardForm
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableJumpsBoundedBy
import AFTD.Kb.Tcs.CslibURMStateIsHaltedIff
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMInstrInstDecidableIsJump
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram
import AFTD.Kb.Tcs.CslibURMInstDecidableIsStraightLine

/-!
# Cslib.URM.Program.instDecidableIsStandardForm

Topic: computability   Node: 0b483c004c93

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.instDecidableIsStandardForm`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/StandardForm.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.Program.instDecidableIsStandardForm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.Program.instDecidableIsStandardForm (p : Program) : Decidable p.IsStandardForm :=
  inferInstanceAs (Decidable (∀ instr ∈ p, instr.JumpsBoundedBy p.length))
