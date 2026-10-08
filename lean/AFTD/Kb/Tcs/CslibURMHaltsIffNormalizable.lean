import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMHalts
import AFTD.Kb.Tcs.RelationNormalizable
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMIsHaltedIffNormal
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.halts_iff_normalizable

Topic: computability   Node: e7487c59892b

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.halts_iff_normalizable`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Halting is equivalent to normalizability in the reduction system.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Halting is equivalent to normalizability in the reduction system. -/
theorem Cslib.URM.halts_iff_normalizable {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Relation.Normalizable (Step p) (State.init inputs) := by
  grind [Halts, isHalted_iff_normal]
