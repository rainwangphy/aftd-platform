import AFTD.Prelude
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationEmptyHRelation
import AFTD.Kb.Tcs.RelationEmptyHRelationEmptyRelation
import AFTD.Kb.Tcs.RelationEmptyHrelationApply
import AFTD.Kb.Tcs.RelationMemCod
import AFTD.Kb.Tcs.RelationDomEmpty

/-!
# Relation.cod_empty

Topic: computability   Node: b912afa9dbd0

Provenance: formalization of a published result. Source: CSLib, `Relation.cod_empty`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.cod_empty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
@[simp, grind =]
lemma Relation.cod_empty : cod (emptyHRelation : α → β → Prop) = ∅ := by grind
