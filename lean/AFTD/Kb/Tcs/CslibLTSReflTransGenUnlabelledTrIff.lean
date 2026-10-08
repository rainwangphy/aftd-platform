import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTSCanReach
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrStepR
import AFTD.Kb.Tcs.CslibLTSMTrToReflTransGen
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff
import AFTD.Kb.Tcs.CslibLTSCanReachRefl

/-!
# Cslib.LTS.reflTransGen_unlabelledTr_iff

Topic: computability   Node: 337fb9b87e3e

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.reflTransGen_unlabelledTr_iff`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The reflexive-transitive closure of the underlying unlabelled transition relation is exactly reachability in the LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
variable (lts : LTS State Label) in
/-- The reflexive-transitive closure of the underlying unlabelled transition relation is exactly reachability in the LTS. -/
theorem Cslib.LTS.reflTransGen_unlabelledTr_iff :
    Relation.ReflTransGen lts.UnlabelledTr s1 s2 ↔ lts.CanReach s1 s2 := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], .refl⟩
    | tail _ htr ih =>
        obtain ⟨μs, hmtr⟩ := ih
        obtain ⟨μ, htr⟩ := htr
        exact ⟨μs ++ [μ], hmtr.stepR lts htr⟩
  · rintro ⟨μs, hmtr⟩
    exact hmtr.toReflTransGen lts
