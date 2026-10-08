import AFTD.Prelude
import AFTD.Kb.Tcs.RelationDom
import AFTD.Kb.Tcs.RelationMemDom

/-!
# Relation.of_dom

Topic: computability   Node: e5a869eef20e

Provenance: formalization of a published result. Source: CSLib, `Relation.of_dom`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.of_dom
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
theorem Relation.of_dom (hab : r a b) : a ∈ dom r := by grind
