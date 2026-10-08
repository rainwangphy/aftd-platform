import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMRegsOutput
import AFTD.Kb.Tcs.CslibURMEvalState
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.eval

Topic: computability   Node: 21bc005b47c1

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.eval`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Evaluation as a partial function using `Part`. Defined when the program halts, returning the value in register 0.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Evaluation as a partial function using `Part`. Defined when the program halts, returning the value in register 0. -/
noncomputable def Cslib.URM.eval (inputs : List ℕ) : Part ℕ :=
  (evalState p inputs).map (·.regs.output)
