import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.selfLoopLTS

Topic: computability   Node: c6858ebe568e

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.selfLoopLTS`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The self-loop LTS has a transition from its unique state to itself.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The self-loop LTS has a transition from its unique state to itself. -/
def Cslib.LTS.Example.selfLoopLTS : LTS Unit Unit where
  Tr _ _ _ := True
