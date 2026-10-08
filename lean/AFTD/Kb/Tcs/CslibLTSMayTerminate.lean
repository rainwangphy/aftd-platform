import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSCanReach
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.MayTerminate

Topic: computability   Node: 33b3b50a998c

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MayTerminate`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Termination.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state 'may terminate' if it can reach a terminated state. The definition of `Terminated` is a parameter.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) (Terminated : State → Prop) in
/-- A state 'may terminate' if it can reach a terminated state. The definition of `Terminated` is a parameter. -/
def Cslib.LTS.MayTerminate (s : State) : Prop := ∃ s', Terminated s' ∧ lts.CanReach s s'
