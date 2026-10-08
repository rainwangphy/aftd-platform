import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.Instr.maxRegister

Topic: computability   Node: 15299f7822a2

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.maxRegister`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The maximum register index referenced by an instruction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The maximum register index referenced by an instruction. -/
@[scoped grind =]
def Cslib.URM.Instr.maxRegister : Instr → ℕ
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n
