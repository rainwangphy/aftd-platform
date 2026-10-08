import AFTD.Prelude
import AFTD.Kb.Tcs.RelationEmptyHRelation

/-!
# Relation.emptyHRelation_emptyRelation

Topic: computability   Node: 22f769cec1ac

Provenance: formalization of a published result. Source: CSLib, `Relation.emptyHRelation_emptyRelation`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.emptyHRelation_emptyRelation
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp, grind =]
theorem Relation.emptyHRelation_emptyRelation : (emptyHRelation : α → α → Prop) = emptyRelation := rfl
