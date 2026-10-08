import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.Instr.writesTo

Topic: computability   Node: 3c76daf438c4

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.writesTo`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The register written to by an instruction, if any.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The register written to by an instruction, if any. -/
@[scoped grind =]
def Cslib.URM.Instr.writesTo : Instr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none
