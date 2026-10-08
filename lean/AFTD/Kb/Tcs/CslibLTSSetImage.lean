import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSImage

/-!
# Cslib.LTS.setImage

Topic: computability   Node: 412e82c69695

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.setImage`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The `μ`-image of a set of states `S` is the union of all `μ`-images of the states in `S`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- The `μ`-image of a set of states `S` is the union of all `μ`-images of the states in `S`. -/
@[grind =]
def Cslib.LTS.setImage (S : Set State) (μ : Label) : Set State :=
  ⋃ s ∈ S, lts.image s μ
