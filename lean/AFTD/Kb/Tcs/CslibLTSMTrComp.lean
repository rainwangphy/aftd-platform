import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff

/-!
# Cslib.LTS.MTr.comp

Topic: computability   Node: 53aff623015b

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.comp`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Multistep transitions can be composed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Multistep transitions can be composed. -/
@[grind <=]
theorem Cslib.LTS.MTr.comp {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label} {s3 : State} :
  lts.MTr s1 μs1 s2 → lts.MTr s2 μs2 s3 →
  lts.MTr s1 (μs1 ++ μs2) s3 := by
  intro h1 h2
  induction h1
  case refl => assumption
  case stepL s1 μ s' μs1' s'' h1' h3 ih  =>
    apply MTr.stepL
    · exact h1'
    · apply ih h2
