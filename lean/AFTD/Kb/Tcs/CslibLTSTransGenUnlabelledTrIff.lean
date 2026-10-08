import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrSingle
import AFTD.Kb.Tcs.CslibLTSMTrStepR
import AFTD.Kb.Tcs.CslibLTSMTrToTransGen
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.transGen_unlabelledTr_iff

Topic: computability   Node: 169836c59309

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.transGen_unlabelledTr_iff`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The transitive closure of the underlying unlabelled transition relation is exactly the nonempty multistep transitions of the LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
variable (lts : LTS State Label) in
/-- The transitive closure of the underlying unlabelled transition relation is exactly the nonempty multistep transitions of the LTS. -/
theorem Cslib.LTS.transGen_unlabelledTr_iff :
    Relation.TransGen lts.UnlabelledTr s1 s2 ↔
      ∃ μs, μs ≠ [] ∧ lts.MTr s1 μs s2 := by
  constructor
  · intro h
    induction h with
    | single htr =>
        obtain ⟨μ, htr⟩ := htr
        exact ⟨[μ], by simp, MTr.single lts htr⟩
    | tail _ htr ih =>
        obtain ⟨μs, hne, hmtr⟩ := ih
        obtain ⟨μ, htr⟩ := htr
        exact ⟨μs ++ [μ], by simp, hmtr.stepR lts htr⟩
  · rintro ⟨μs, hne, hmtr⟩
    exact hmtr.toTransGen lts hne
