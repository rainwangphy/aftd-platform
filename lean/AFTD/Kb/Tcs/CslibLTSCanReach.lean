import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.CanReach

Topic: computability   Node: 616bb32072f5

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.CanReach`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A state `s1` can reach a state `s2` if there exists a multistep transition from `s1` to `s2`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- A state `s1` can reach a state `s2` if there exists a multistep transition from `s1` to `s2`. -/
@[grind =]
def Cslib.LTS.CanReach (s1 s2 : State) : Prop :=
  ∃ μs, lts.MTr s1 μs s2
