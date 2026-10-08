import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff

/-!
# Cslib.LTS.MTr.cons_iff

Topic: computability   Node: c5e08d6f7aea

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.cons_iff`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multistep transition along `μ :: μs` is a transition labelled by `μ` plus a multistep transition labelled by `μs`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- A multistep transition along `μ :: μs` is a transition labelled by `μ` plus a multistep transition labelled by `μs`. -/
theorem Cslib.LTS.MTr.cons_iff {lts : LTS State Label} :
    lts.MTr s1 (μ :: μs) s2 ↔ ∃ s, lts.Tr s1 μ s ∧ lts.MTr s μs s2 := by
  constructor
  · rintro (_ | ⟨htr, hmtr⟩)
    exact ⟨_, htr, hmtr⟩
  · intro ⟨s, htr, hmtr⟩
    exact .stepL htr hmtr
