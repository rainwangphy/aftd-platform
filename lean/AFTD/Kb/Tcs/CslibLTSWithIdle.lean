import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.withIdle

Topic: computability   Node: dcc5000909c6

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.withIdle`. Lean proof by Ayberk Tosun, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/LTSCat/Basic.lean (Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved, Apache-2.0); 1 verbatim; compiled here.

We first define what is denoted Tran* in [WinskelNielsen1995]: the extension of a transition relation with idle transitions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- We first define what is denoted Tran* in [WinskelNielsen1995]: the extension of a transition relation with idle transitions. -/
def Cslib.LTS.withIdle (lts : LTS State Label) : LTS State (Option Label) :=
  ⟨fun s l s' => l.elim (s = s') (lts.Tr s · s')⟩
