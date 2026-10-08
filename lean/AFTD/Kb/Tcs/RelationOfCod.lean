import AFTD.Prelude
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationMemCod

/-!
# Relation.of_cod

Topic: computability   Node: 58833ff5379d

Provenance: formalization of a published result. Source: CSLib, `Relation.of_cod`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.of_cod
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
theorem Relation.of_cod (hab : r a b) : b ∈ cod r := by grind
