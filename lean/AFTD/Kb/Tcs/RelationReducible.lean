import AFTD.Prelude

/-!
# Relation.Reducible

Topic: computability   Node: 52ff03e2418f

Provenance: formalization of a published result. Source: CSLib, `Relation.Reducible`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element is reducible with respect to a relation if there is a value it is related to.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An element is reducible with respect to a relation if there is a value it is related to. -/
abbrev Relation.Reducible (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y
