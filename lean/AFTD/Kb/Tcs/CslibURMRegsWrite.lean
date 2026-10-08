import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMRegs

/-!
# Cslib.URM.Regs.write

Topic: computability   Node: 2a8d45a92815

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Regs.write`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Write value v to register n.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Write value v to register n. -/
@[scoped grind =]
def Cslib.URM.Regs.write (σ : Regs) (n : ℕ) (v : ℕ) : Regs := Function.update σ n v
