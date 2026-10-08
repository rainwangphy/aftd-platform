import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.countdownLTS

Topic: computability   Node: 1d7bdb9920b0

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.countdownLTS`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The countdown LTS takes a natural number to its predecessor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The countdown LTS takes a natural number to its predecessor. -/
def Cslib.LTS.Example.countdownLTS : LTS ℕ Unit where
  Tr n _ m := n = m + 1
