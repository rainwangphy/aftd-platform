import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSImageMultistep
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.setImageMultistep

Topic: computability   Node: 06739662168c

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.setImageMultistep`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The `μs`-image of a set of states `S`, where `μs` is a list of labels, is the union of all `μs`-images of the states in `S`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- The `μs`-image of a set of states `S`, where `μs` is a list of labels, is the union of all `μs`-images of the states in `S`. -/
@[grind =]
def Cslib.LTS.setImageMultistep (S : Set State) (μs : List Label) : Set State :=
  ⋃ s ∈ S, lts.imageMultistep s μs
