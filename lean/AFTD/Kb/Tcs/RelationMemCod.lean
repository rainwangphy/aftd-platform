import AFTD.Prelude
import AFTD.Kb.Tcs.RelationCod

/-!
# Relation.mem_cod

Topic: computability   Node: 001265b5beca

Provenance: formalization of a published result. Source: CSLib, `Relation.mem_cod`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.mem_cod
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
@[simp, grind =] lemma Relation.mem_cod : b ∈ cod r ↔ ∃ a, r a b := .rfl
