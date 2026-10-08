import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.Instr.readsFrom

Topic: computability   Node: 2a4bf84cf91b

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr.readsFrom`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The registers read by an instruction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The registers read by an instruction. -/
@[scoped grind =]
def Cslib.URM.Instr.readsFrom : Instr → Finset ℕ
  | Z _ => ∅
  | S n => {n}
  | T m _ => {m}
  | J m n _ => {m, n}
