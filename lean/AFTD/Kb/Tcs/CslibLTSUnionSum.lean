import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSUnionSubtype
import AFTD.Kb.Tcs.CslibLTSInl
import AFTD.Kb.Tcs.CslibLTSInr

/-!
# Cslib.LTS.unionSum

Topic: computability   Node: d7029c657bb8

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.unionSum`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Union.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Union of two LTSs with the same `Label` type. The result combines the original respective state types `State1` and `State2` into `(State1 ⊕ State2)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
variable {State : Type u} {Label : Type v} in
/-- Union of two LTSs with the same `Label` type. The result combines the original respective state types `State1` and `State2` into `(State1 ⊕ State2)`. -/
def Cslib.LTS.unionSum (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    LTS (State1 ⊕ State2) Label :=
  unionSubtype lts1.inl lts2.inr
