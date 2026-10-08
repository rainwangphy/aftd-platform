import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.TrInv

Topic: computability   Node: 2af10004b8b5

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.TrInv`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Single-step invariant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Single-step invariant. -/
@[grind =]
def Cslib.LTS.TrInv (p : State → Prop) : Prop :=
  ∀ s1 μ s2, lts.Tr s1 μ s2 → p s1 → p s2
