import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.image

Topic: computability   Node: afbf60b7a7a8

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.image`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The `μ`-image of a state `s` is the set of all `μ`-derivatives of `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- The `μ`-image of a state `s` is the set of all `μ`-derivatives of `s`. -/
@[grind =]
def Cslib.LTS.image (s : State) (μ : Label) : Set State := { s' : State | lts.Tr s μ s' }
