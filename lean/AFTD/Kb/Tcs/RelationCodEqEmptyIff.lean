import AFTD.Prelude
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationEmptyHRelation
import AFTD.Kb.Tcs.RelationEmptyHrelationApply
import AFTD.Kb.Tcs.RelationEmptyHRelationEmptyRelation
import AFTD.Kb.Tcs.RelationMemCod
import AFTD.Kb.Tcs.RelationDomEmpty
import AFTD.Kb.Tcs.RelationCodEmpty
import AFTD.Kb.Tcs.RelationDomEqEmptyIff

/-!
# Relation.cod_eq_empty_iff

Topic: computability   Node: 3783ac84c546

Provenance: formalization of a published result. Source: CSLib, `Relation.cod_eq_empty_iff`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.cod_eq_empty_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
@[simp, grind =]
lemma Relation.cod_eq_empty_iff : cod r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a b
    simp
    grind => have : b ∈ cod r; finish
  mpr h := by grind
