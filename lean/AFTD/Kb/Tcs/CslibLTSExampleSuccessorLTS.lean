import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.successorLTS

Topic: computability   Node: c8a3fed753ee

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.successorLTS`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The successor LTS takes each natural number to its successor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The successor LTS takes each natural number to its successor. -/
def Cslib.LTS.Example.successorLTS : LTS ℕ Unit where
  Tr n _ m := m = n + 1
