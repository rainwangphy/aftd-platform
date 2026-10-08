import AFTD.Prelude
import AFTD.Kb.Tcs.RelationSerial

/-!
# Relation.refl_serial

Topic: computability   Node: bb1d1c5a6bf8

Provenance: formalization of a published result. Source: CSLib, `Relation.refl_serial`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Euclidean.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.refl_serial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relator in
variable {α : Type*} {r : α → α → Prop} in
@[scoped grind →]
lemma Relation.refl_serial (r : α → α → Prop) (h : Std.Refl r) : Serial r where
  serial a := ⟨a, h.refl a⟩
