import AFTD.Prelude

/-!
# Relation.dom

Topic: computability   Node: 3b010ead88e2

Provenance: formalization of a published result. Source: CSLib, `Relation.dom`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Domain of a relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Domain of a relation. -/
def Relation.dom (r : α → β → Prop) : Set α := {a | ∃ b, r a b}
