import AFTD.Prelude

/-!
# Relation.Terminating

Topic: computability   Node: ea3cf1c35f4a

Provenance: formalization of a published result. Source: CSLib, `Relation.Terminating`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is terminating when the inverse of its transitive closure is well-founded. Note that this is also called Noetherian or strongly normalizing in the literature.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is terminating when the inverse of its transitive closure is well-founded. Note that this is also called Noetherian or strongly normalizing in the literature. -/
abbrev Relation.Terminating (r : α → α → Prop) := WellFounded (fun a b => r b a)
