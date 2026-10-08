import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Stuck

Topic: computability   Node: 3ec8e5e8857f

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Stuck`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Termination.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated` is a parameter.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) (Terminated : State → Prop) in
/-- A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated` is a parameter. -/
def Cslib.LTS.Stuck (s : State) : Prop :=
  ¬Terminated s ∧ ¬∃ μ s', lts.Tr s μ s'
