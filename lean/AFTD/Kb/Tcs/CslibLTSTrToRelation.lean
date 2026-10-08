import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Tr.toRelation

Topic: computability   Node: 8c22e9b83519

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Tr.toRelation`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Returns the relation that relates all states `s1` and `s2` via a fixed transition label `μ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- Returns the relation that relates all states `s1` and `s2` via a fixed transition label `μ`. -/
def Cslib.LTS.Tr.toRelation (lts : LTS State Label) (μ : Label) : State → State → Prop :=
  fun s1 s2 => lts.Tr s1 μ s2
