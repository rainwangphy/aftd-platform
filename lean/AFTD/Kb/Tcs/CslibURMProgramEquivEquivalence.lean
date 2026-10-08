import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMProgramEquiv
import AFTD.Kb.Tcs.CslibURMEval
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.ProgramEquiv.equivalence

Topic: computability   Node: b4d478f8eee3

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.ProgramEquiv.equivalence`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Program equivalence is an equivalence relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Program equivalence is an equivalence relation. -/
theorem Cslib.URM.ProgramEquiv.equivalence : Equivalence ProgramEquiv where
  refl := fun _ _ => rfl
  symm := fun h inputs => (h inputs).symm
  trans := fun h₁ h₂ inputs => (h₁ inputs).trans (h₂ inputs)
