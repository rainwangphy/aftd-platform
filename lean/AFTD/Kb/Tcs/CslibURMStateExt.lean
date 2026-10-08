import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMRegsWriteReadSelf
import AFTD.Kb.Tcs.CslibURMRegsWriteReadOfNe
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.State.ext

Topic: computability   Node: 41aac8c11b54

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.ext`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extensionality for State: two states are equal iff their components are equal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Extensionality for State: two states are equal iff their components are equal. -/
@[ext]
theorem Cslib.URM.State.ext {s₁ s₂ : State} (hpc : s₁.pc = s₂.pc) (hregs : s₁.regs = s₂.regs) : s₁ = s₂ := by
  cases s₁; cases s₂; simp only at hpc hregs; simp [hpc, hregs]
