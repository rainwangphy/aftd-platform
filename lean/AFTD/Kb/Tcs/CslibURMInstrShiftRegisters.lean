import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.Instr.shiftRegisters

Topic: computability   Node: 1cc42b6b6349

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.shiftRegisters`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shift all register references in an instruction by `offset`. Used to isolate register usage when composing programs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Shift all register references in an instruction by `offset`. Used to isolate register usage when composing programs. -/
@[scoped grind =]
def Cslib.URM.Instr.shiftRegisters (offset : ℕ) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q
