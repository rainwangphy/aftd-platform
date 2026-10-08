import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Step.no_step_of_halted

Topic: computability   Node: 118291ed1a4d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step.no_step_of_halted`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A halted state has no successor in the step relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
variable {p : Program} in
/-- A halted state has no successor in the step relation. -/
theorem Cslib.URM.Step.no_step_of_halted {s s' : State} (hhalted : s.isHalted p) : ¬Step p s s' := by
  grind [State.isHalted]
