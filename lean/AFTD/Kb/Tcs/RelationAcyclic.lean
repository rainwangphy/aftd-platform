import AFTD.Prelude

/-!
# Relation.Acyclic

Topic: computability   Node: c5d00ceb2228

Provenance: formalization of a published result. Source: CSLib, `Relation.Acyclic`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is acyclic if its transitive closure is irreflexive, equivalently if it admits no nonempty cycle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is acyclic if its transitive closure is irreflexive, equivalently if it admits no nonempty cycle. -/
abbrev Relation.Acyclic (r : α → α → Prop) := Std.Irrefl (TransGen r)
