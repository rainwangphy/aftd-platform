import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Halts

Topic: computability   Node: 4c9cede85809

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Halts`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A program halts on given inputs if execution reaches a halted state. This is equivalent to `(Step p).Normalizable (State.init inputs)` — see `halts_iff_normalizable`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- A program halts on given inputs if execution reaches a halted state. This is equivalent to `(Step p).Normalizable (State.init inputs)` — see `halts_iff_normalizable`. -/
def Cslib.URM.Halts (inputs : List ℕ) : Prop :=
  ∃ s, Steps p (State.init inputs) s ∧ s.isHalted p
