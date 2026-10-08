import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMHalts
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.evalState

Topic: computability   Node: 2f992cbf51d3

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.evalState`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Evaluation returning the full halting state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Evaluation returning the full halting state. -/
noncomputable def Cslib.URM.evalState (inputs : List ℕ) : Part State :=
  ⟨Halts p inputs, fun h => Classical.choose h⟩
