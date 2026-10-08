import AFTD.Prelude
import AFTD.Kb.Tcs.RelationSerial
import AFTD.Kb.Tcs.RelationReflSerial

/-!
# Relation.instSerialOfRefl

Topic: computability   Node: 8fd7adf6b146

Provenance: formalization of a published result. Source: CSLib, `Relation.instSerialOfRefl`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Euclidean.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.instSerialOfRefl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relator in
variable {α : Type*} {r : α → α → Prop} in
instance Relation.instSerialOfRefl [instRefl : Std.Refl r] : Serial r := refl_serial r instRefl
