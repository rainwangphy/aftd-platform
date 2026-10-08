import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.MTr.split

Topic: computability   Node: 03b62934cbbc

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.split`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multistep transition over a concatenation can be split into two multistep transitions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- A multistep transition over a concatenation can be split into two multistep transitions. -/
theorem Cslib.LTS.MTr.split {lts : LTS State Label} (h : lts.MTr s1 (μs ++ μs') s2) :
    ∃ s, lts.MTr s1 μs s ∧ lts.MTr s μs' s2 := by
  induction μs generalizing s1 s2 with
  | nil => use s1, .refl, h
  | cons μ μs ih =>
    rw [List.cons_append] at h
    cases h
    case stepL s htr hmtr =>
      obtain ⟨s', hmtr', hmtr''⟩ := ih hmtr
      use s', .stepL htr hmtr', hmtr''
