import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMRegs

/-!
# Cslib.URM.Regs.ofInputs

Topic: computability   Node: daf28d60a94d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Regs.ofInputs`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Initialize registers with input values in registers 0, 1, ..., k-1. Registers beyond the inputs are initialized to 0.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Initialize registers with input values in registers 0, 1, ..., k-1. Registers beyond the inputs are initialized to 0. -/
@[scoped grind =]
def Cslib.URM.Regs.ofInputs (inputs : List ℕ) : Regs := fun n => inputs.getD n 0
