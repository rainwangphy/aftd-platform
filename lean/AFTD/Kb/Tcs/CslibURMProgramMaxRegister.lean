import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrMaxRegister

/-!
# Cslib.URM.Program.maxRegister

Topic: computability   Node: a35669f37865

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Program.maxRegister`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The maximum register index referenced by any instruction in the program.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The maximum register index referenced by any instruction in the program. -/
@[scoped grind =]
def Cslib.URM.Program.maxRegister (p : Program) : ℕ :=
  p.foldl (fun acc instr => max acc instr.maxRegister) 0
