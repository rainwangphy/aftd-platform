import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMHalts
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Diverges

Topic: computability   Node: 34fd137bfb7d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Diverges`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A program diverges on given inputs if it does not halt.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- A program diverges on given inputs if it does not halt. -/
def Cslib.URM.Diverges (inputs : List ℕ) : Prop := ¬Halts p inputs
