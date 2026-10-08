import AFTD.Prelude

/-!
# Relation.cod

Topic: computability   Node: e10d70fd9195

Provenance: formalization of a published result. Source: CSLib, `Relation.cod`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Codomain of a relation, aka range.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Codomain of a relation, aka range. -/
def Relation.cod (r : α → β → Prop) : Set β := {b | ∃ a, r a b}
