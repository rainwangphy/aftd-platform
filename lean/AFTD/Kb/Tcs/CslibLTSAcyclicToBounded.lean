import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSAcyclic
import AFTD.Kb.Tcs.CslibLTSBounded
import AFTD.Kb.Tcs.CslibLTSBoundedUpTo
import AFTD.Kb.Tcs.CslibLTSAcyclicToBoundedUpTo
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.Acyclic.toBounded

Topic: computability   Node: 4696de15a28e

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Acyclic.toBounded`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Termination.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On a finite state space, acyclic LTSs are bounded.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) (Terminated : State → Prop) in
/-- On a finite state space, acyclic LTSs are bounded. -/
theorem Cslib.LTS.Acyclic.toBounded [Finite State] (h : lts.Acyclic) : lts.Bounded :=
  ⟨Nat.card State, h.toBoundedUpTo⟩
