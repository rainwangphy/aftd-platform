import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMRegs

/-!
# Cslib.URM.Regs.read

Topic: computability   Node: a29c7d8050fc

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Regs.read`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Read the contents of register n.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Read the contents of register n. -/
@[scoped grind =]
def Cslib.URM.Regs.read (σ : Regs) (n : ℕ) : ℕ := σ n
