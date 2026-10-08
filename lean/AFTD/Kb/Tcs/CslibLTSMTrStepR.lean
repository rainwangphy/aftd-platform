import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrSingle
import AFTD.Kb.Tcs.CslibLTSMTrNilIff

/-!
# Cslib.LTS.MTr.stepR

Topic: computability   Node: 272a586e6f34

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.stepR`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any multistep transition can be extended by adding a transition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Any multistep transition can be extended by adding a transition. -/
theorem Cslib.LTS.MTr.stepR {s1 : State} {μs : List Label} {s2 : State} {μ : Label} {s3 : State} :
  lts.MTr s1 μs s2 → lts.Tr s2 μ s3 → lts.MTr s1 (μs ++ [μ]) s3 := by
  intro h1 h2
  induction h1
  case refl s1' => exact MTr.single lts h2
  case stepL s1' μ' s2' μs' s3' h1' h3 ih =>
    apply MTr.stepL
    · exact h1'
    · apply ih h2
