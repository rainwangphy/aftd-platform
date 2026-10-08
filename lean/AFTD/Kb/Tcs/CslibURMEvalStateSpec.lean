import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMEvalState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.evalState_spec

Topic: computability   Node: 91ddf10e2194

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.evalState_spec`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Specification: the state from evalState satisfies Steps and isHalted.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Specification: the state from evalState satisfies Steps and isHalted. -/
theorem Cslib.URM.evalState_spec {inputs : List ℕ} (h : (evalState p inputs).Dom) :
    let s := (evalState p inputs).get h
    Steps p (State.init inputs) s ∧ s.isHalted p :=
  Classical.choose_spec h
