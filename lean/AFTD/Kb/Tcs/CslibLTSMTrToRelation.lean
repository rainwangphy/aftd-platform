import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.MTr.toRelation

Topic: computability   Node: 1be20392c6f5

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.toRelation`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Returns the relation that relates all states `s1` and `s2` via a fixed list of transition labels `μs`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
/-- Returns the relation that relates all states `s1` and `s2` via a fixed list of transition labels `μs`. -/
def Cslib.LTS.MTr.toRelation (lts : LTS State Label) (μs : List Label) : State → State → Prop :=
  fun s1 s2 => lts.MTr s1 μs s2
