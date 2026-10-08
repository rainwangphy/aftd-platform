import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMRegs

/-!
# Cslib.URM.State

Topic: computability   Node: e448219b7f3a

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Machine state: program counter (0-indexed) and register contents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Machine state: program counter (0-indexed) and register contents. -/
structure Cslib.URM.State where
  /-- Program counter (0-indexed). -/
  pc : ℕ
  /-- Register contents. -/
  regs : Regs
