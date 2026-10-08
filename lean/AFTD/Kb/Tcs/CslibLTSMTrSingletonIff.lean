import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrSingleInvert
import AFTD.Kb.Tcs.CslibLTSMTrSingle
import AFTD.Kb.Tcs.CslibLTSMTrNilIff

/-!
# Cslib.LTS.MTr.singleton_iff

Topic: computability   Node: c6470bd53de1

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.singleton_iff`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 1-sized multistep transition is exactly a single transition with the given label.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- A 1-sized multistep transition is exactly a single transition with the given label. -/
@[simp] theorem Cslib.LTS.MTr.singleton_iff (s1 : State) (μ : Label) (s2 : State) :
  lts.MTr s1 [μ] s2 ↔ lts.Tr s1 μ s2 := ⟨MTr.single_invert lts s1 μ s2, MTr.single lts⟩
