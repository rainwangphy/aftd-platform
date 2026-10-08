import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.Instr.shiftJumps

Topic: computability   Node: 9b5354b68e31

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.shiftJumps`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shift all jump targets in an instruction by `offset`. Used when concatenating programs to maintain correct jump destinations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Shift all jump targets in an instruction by `offset`. Used when concatenating programs to maintain correct jump destinations. -/
@[scoped grind =]
def Cslib.URM.Instr.shiftJumps (offset : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)
