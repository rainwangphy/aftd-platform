import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.State.isHalted_iff

Topic: computability   Node: 0675d20e4f3a

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.isHalted_iff`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.State.isHalted_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
theorem Cslib.URM.State.isHalted_iff (s : State) (p : Program) : s.isHalted p ↔ p.length ≤ s.pc := Iff.rfl
