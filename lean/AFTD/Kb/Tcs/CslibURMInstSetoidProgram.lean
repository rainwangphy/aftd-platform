import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramEquiv
import AFTD.Kb.Tcs.CslibURMProgramEquivEquivalence
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.instSetoidProgram

Topic: computability   Node: 8899b6579de5

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.instSetoidProgram`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Setoid instance for programs, enabling the ≈ notation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Setoid instance for programs, enabling the ≈ notation. -/
instance Cslib.URM.instSetoidProgram : Setoid Program := Setoid.mk _ ProgramEquiv.equivalence
