import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMRegsOutput
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.HaltsWithResult

Topic: computability   Node: 51df41ba2c8c

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.HaltsWithResult`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A program halts on given inputs with a specific result in R[0].
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- A program halts on given inputs with a specific result in R[0]. -/
def Cslib.URM.HaltsWithResult (inputs : List ℕ) (result : ℕ) : Prop :=
  ∃ s, Steps p (State.init inputs) s ∧ s.isHalted p ∧ s.regs.output = result
