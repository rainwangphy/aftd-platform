import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTSMTrToReflTransGen
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.MTr.toTransGen

Topic: computability   Node: 5284a03eeefc

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.toTransGen`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonempty multistep transition induces a nonempty path in the underlying unlabelled transition relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
variable (lts : LTS State Label) in
/-- A nonempty multistep transition induces a nonempty path in the underlying unlabelled transition relation. -/
theorem Cslib.LTS.MTr.toTransGen (h : lts.MTr s1 μs s2) (hne : μs ≠ []) :
    Relation.TransGen lts.UnlabelledTr s1 s2 := by
  cases h with
  | refl => contradiction
  | stepL htr hmtr => exact Relation.TransGen.head' ⟨_, htr⟩ (hmtr.toReflTransGen lts)
