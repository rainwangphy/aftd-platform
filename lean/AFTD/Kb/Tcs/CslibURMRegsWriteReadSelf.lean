import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMRegsWrite

/-!
# Cslib.URM.Regs.write_read_self

Topic: computability   Node: 66969f0876c6

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Regs.write_read_self`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.Regs.write_read_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp, scoped grind =]
theorem Cslib.URM.Regs.write_read_self (σ : Regs) (n v : ℕ) : (σ.write n v).read n = v := by
  simp only [write, read, Function.update_self]
