import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Step.deterministic

Topic: computability   Node: 0163e4ca6949

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step.deterministic`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The step relation is deterministic: each state has at most one successor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
variable {p : Program} in
set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- The step relation is deterministic: each state has at most one successor. -/
theorem Cslib.URM.Step.deterministic : Relator.RightUnique (Step p) := by grind only [Relator.RightUnique]
