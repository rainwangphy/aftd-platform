import AFTD.Prelude

/-!
# Cslib.Computability.Turing.SingleTape.TrLabel

Topic: computability   Node: feccab494273

Provenance: formalization of a published result. Source: CSLib, `Cslib.Computability.Turing.SingleTape.TrLabel`. Lean proof by Fabrizio Montesi, Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Defs.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The transition labels used by a single-tape Turing Machine.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The transition labels used by a single-tape Turing Machine. -/
inductive Cslib.Computability.Turing.SingleTape.TrLabel (Symbol : Type*)
  /-- Read `x` from the tape. -/ | read (x : Symbol)
  /-- Write `x` on the tape. -/
  | write (x : Symbol)
  /-- Move the head of the tape. -/
  | move (d : Turing.Dir)
  /-- Do nothing. -/
  | skip
