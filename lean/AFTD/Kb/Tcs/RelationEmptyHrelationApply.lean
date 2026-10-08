import AFTD.Prelude
import AFTD.Kb.Tcs.RelationEmptyHRelation
import AFTD.Kb.Tcs.RelationEmptyHRelationEmptyRelation

/-!
# Relation.emptyHrelation_apply

Topic: computability   Node: e6a67d465aaa

Provenance: formalization of a published result. Source: CSLib, `Relation.emptyHrelation_apply`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.emptyHrelation_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp, grind =]
theorem Relation.emptyHrelation_apply (a : α) (b : β) : emptyHRelation a b ↔ False := .rfl
