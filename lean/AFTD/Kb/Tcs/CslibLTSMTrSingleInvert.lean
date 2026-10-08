import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff

/-!
# Cslib.LTS.MTr.single_invert

Topic: computability   Node: 1665082f9db8

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.single_invert`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Any 1-sized multistep transition implies a transition with the same states and label.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Any 1-sized multistep transition implies a transition with the same states and label. -/
@[grind .]
theorem Cslib.LTS.MTr.single_invert (s1 : State) (μ : Label) (s2 : State) :
  lts.MTr s1 [μ] s2 → lts.Tr s1 μ s2 := by
  intro h
  cases h
  case stepL s1' htr hmtr =>
    cases hmtr
    exact htr
