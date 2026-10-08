import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.inr

Topic: computability   Node: bb548e0b3b9c

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.inr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Union.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lifting of an `LTS State Label` to `LTS (State' ⊕ State) Label`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
variable {State : Type u} {Label : Type v} in
/-- Lifting of an `LTS State Label` to `LTS (State' ⊕ State) Label`. -/
def Cslib.LTS.inr (lts : LTS State Label) :
    LTS { x : State' ⊕ State // x.isRight } { _label : Label // True } where
  Tr s μ s' :=
    match s, s' with
    | ⟨.inr s1, _⟩, ⟨.inr s2, _⟩ => lts.Tr s1 μ s2
    | _, _ => False
