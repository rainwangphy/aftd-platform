import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.HasOutLabel

Topic: computability   Node: f29a9c91de3e

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.HasOutLabel`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state has an outgoing label `μ` if it has a `μ`-derivative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- A state has an outgoing label `μ` if it has a `μ`-derivative. -/
def Cslib.LTS.HasOutLabel (s : State) (μ : Label) : Prop :=
  ∃ s', lts.Tr s μ s'
