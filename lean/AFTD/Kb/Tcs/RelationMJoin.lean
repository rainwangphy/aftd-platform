import AFTD.Prelude

/-!
# Relation.MJoin

Topic: computability   Node: 618455b0ce0f

Provenance: formalization of a published result. Source: CSLib, `Relation.MJoin`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The join of the reflexive transitive closure. This is not named in Mathlib, but see `#loogle Relation.Join (Relation.ReflTransGen ?r)`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The join of the reflexive transitive closure. This is not named in Mathlib, but see `#loogle Relation.Join (Relation.ReflTransGen ?r)` -/
abbrev Relation.MJoin (r : α → α → Prop) := Join (ReflTransGen r)
