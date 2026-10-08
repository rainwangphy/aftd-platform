import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.MTr.toReflTransGen

Topic: computability   Node: 94f3a8faacd5

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.toReflTransGen`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multistep transition induces a reflexive-transitive path in the underlying unlabelled transition relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
variable (lts : LTS State Label) in
/-- A multistep transition induces a reflexive-transitive path in the underlying unlabelled transition relation. -/
theorem Cslib.LTS.MTr.toReflTransGen (h : lts.MTr s1 μs s2) :
    Relation.ReflTransGen lts.UnlabelledTr s1 s2 := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact ih.head ⟨_, htr⟩
