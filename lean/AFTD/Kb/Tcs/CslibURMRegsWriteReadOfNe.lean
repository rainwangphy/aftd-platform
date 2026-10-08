import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMRegs
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMRegsWriteReadSelf

/-!
# Cslib.URM.Regs.write_read_of_ne

Topic: computability   Node: 9692386ea2ba

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Regs.write_read_of_ne`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Basic.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.Regs.write_read_of_ne
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp, scoped grind =]
theorem Cslib.URM.Regs.write_read_of_ne (σ : Regs) (m n v : ℕ) (h : m ≠ n) :
    (σ.write n v).read m = σ.read m := by
  simp only [write, read, Function.update_of_ne h]
